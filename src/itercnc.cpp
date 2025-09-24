// Created on: 3 Apr 2025
// Author: Oleg Zaikin
// E-mail: zaikin.icc@gmail.com
//
// Iterative Cube-and-Conquer on n threads.
//
// 1) Produce at most n cubes, run a CDCL solver on them with a conflict-limit.
// 2) Process the results:
//  a) if SAT is found on some cube, stop and return SAT;
//  b) if UNSAT is proven on all cubes, stop and return UNSAT;
//  c) if all but one cubes are solved and UNSAT, stop processing the remaining
//     cube, add negation-clauses for the UNSAT-cubes and one-literal clauses
//     for the unsolved cube to the CNF, go to 1.
//  d) if at least one cube is solved and all solved are UNSAT, add
//     negation-clauses for these cubes to the CNF and go to 1;
//  e) no cubes are solved, stop and return INDET.
//
// Usage : itercnc la-solver cdcl-solver cnf conflict-limit-cube nthreads
//
// Example:
//     ./itercnc ./march ./kissat ./problem.cnf 100000 16
//   iteratively produces at most 16 cubes on problem.cnf and runs kissat on
//   them with the limit of 100000 conflicts.
//=============================================================================

#include <iostream>
#include <string>
#include <fstream>
#include <sstream>
#include <vector>
#include <cassert>
#include <chrono>
#include <thread>
#include <set>
#include <algorithm>

#include <omp.h>

using namespace std;

string version = "0.1.4";

#define cube_t vector<int> 
#define time_point_t chrono::time_point<chrono::system_clock>

enum status{ NOT_STARTED = -1, IN_PROGRESS = 0, PROCESSED = 1};
enum result{ UNSAT = 0, SAT = 1, INTERR = 2 };

struct workunit {
	int id;
	status stts;
	result rslt;
	cube_t cube;
	double time;
	workunit() : id(-1), stts(NOT_STARTED), rslt(INTERR), cube(), time(-1) {};
	void print() {
		for (auto &c : cube) cout << c << " ";
		cout << endl;
	}
};

struct cnf {
	long long int var_num;
	long long int clause_num;
	vector<string> clauses;
	string name;
	cnf() : var_num(0), clause_num(0), clauses() {}
	cnf(string cnf_name) : var_num(0), clause_num(0), clauses(), name(cnf_name) {
		read(name);
	}
	void read(const string cnf_name) {
		var_num = 0;
		clause_num = 0;
		clauses.clear();
		name = cnf_name;
		ifstream cnf_file(name, ios_base::in);
		assert(cnf_file.is_open());
		string str;
		while (getline(cnf_file, str)) {
			if (str.size() == 0 or str[0] == 'p' or str[0] == 'c')
				continue;
			clauses.push_back(str);
			clause_num++;
			stringstream sstream;
			sstream << str;
			long long int ival;
			while (sstream >> ival)	var_num = max(llabs(ival), var_num);
		}
		cnf_file.close();
	}
	void print() {
		cout << "var_num : " << var_num << endl;
		cout << "clause_num : " << clause_num << endl;
		cout << "name : " << name << endl;
	};
};

unsigned get_cutoff(const string la_solver_name,
	                const cnf cur_cnf,
					const unsigned prev_threshold,
	                const unsigned nthreads,
					set<string> interr_cubes_set);
unsigned get_free_vars(const string la_solver_name, const cnf cur_cnf);
string exec(const string cmd_str);
vector<workunit> read_cubes(const string cubes_name);
bool is_empty_file(const string fname);
result solve_cube(const string base_cnf_name, const cnf c,
				  const string solver_name, const time_point_t program_start,
				  workunit &wu, const unsigned cube_time_lim);
result read_solver_result(const string fname);
void print_stats(const workunit wu, const unsigned sat_cubes,
	             const unsigned unsat_cubes, const unsigned interr_cubes);
void kill_solver(const string solver_name);
void print_elapsed_time(const time_point_t program_start);
cnf add_sat_unsat_clauses(cnf cur_cnf, vector<workunit> wu_vec,
	                      const unsigned iter_num,
						  const bool is_add_sat_clause=false);

void print_usage() {
	cout << "Usage : itercnc la-solver cdcl-solver cnf conflict-limit-cube nthreads"
	     << endl;
}

void print_version() {
	cout << "version: " << version << endl;
}

// Form a string representation of a cube (as an array in integers):
string cube_to_str(const cube_t cube) {
	cube_t sorted_cube = cube;
	sort(sorted_cube.begin(), sorted_cube.end());
	assert(sorted_cube == cube);
	string res_str = "";
	for (unsigned i=0; i<cube.size(); i++) {
		res_str += to_string(cube[i]);
		if (i < cube.size()-1) res_str += "+";
	}
	assert(res_str != "");
	return res_str;
}

int main(int argc, char *argv[]) {
    // Read inputs:
    vector<string> str_argv;
	for (int i=0; i < argc; ++i) str_argv.push_back(argv[i]);
	assert(str_argv.size() == argc);
	if (argc == 2 and str_argv[1] == "-h") {
		print_usage();
		exit(EXIT_SUCCESS);
	}
	if (argc == 2 and str_argv[1] == "-v") {
		print_version();
		exit(EXIT_SUCCESS);
	}
	if (argc < 6) {
		print_usage();
		exit(EXIT_FAILURE);
	}

	string la_solver_name = str_argv[1];
    string cdcl_solver_name = str_argv[2];
	string cnf_name = str_argv[3];
	unsigned cube_conflict_lim = stoi(str_argv[4]);
	unsigned nthreads = stoi(str_argv[5]);
	const unsigned system_nthreads = thread::hardware_concurrency();
	if (nthreads > system_nthreads) {
		cout << "Warning : " << system_nthreads << " threads in total, but "
		     << nthreads << " threads are requested." << endl;
	}
	cout << "lookahead solver : "           << la_solver_name    << endl;
	cout << "CDCL solver : "                << cdcl_solver_name  << endl;
	cout << "cnf : "                        << cnf_name          << endl;
	cout << "cube_conflict_limit : "        << cube_conflict_lim << endl;
	cout << "number of threads : "          << nthreads          << endl;

	cout << endl;
	cout << "Reading CNF " << cnf_name << endl;
	cnf cur_cnf(cnf_name);
	cur_cnf.print();

	size_t pos_cnf = cnf_name.find(".cnf");
	assert(pos_cnf != string::npos);
	string base_cnf_name = cnf_name.substr(0, pos_cnf);

	const time_point_t program_start = chrono::system_clock::now();

    // Run CnC interatively:
	unsigned iter_num = 0;
	unsigned prev_threshold = 0;
	unsigned threshold = 0;
	set<string> interr_cubes_set;
	for (;;) {
		cout << "*** iteration " << iter_num << endl;
		// Find a proper cutoff threshold for cubing:
		cout << "prev_threshold : " << prev_threshold << endl;
		threshold = get_cutoff(la_solver_name, cur_cnf, prev_threshold, nthreads, interr_cubes_set);
		prev_threshold = threshold;
		// Produce cubes:
		string cubes_name = "cubes";
		string system_str = la_solver_name + " " + cur_cnf.name + " -n " + to_string(threshold) + " -o " + cubes_name;
		exec(system_str);
		vector<workunit> wu_vec = read_cubes(cubes_name);
		vector<workunit> nontried_wu_vec;
		for (auto &wu : wu_vec) {
			string cube_str = cube_to_str(wu.cube);
			if (interr_cubes_set.find(cube_str) == interr_cubes_set.end()) {
				nontried_wu_vec.push_back(wu);
			}
		}
		cout << "threshold : " << threshold << " gives " << nontried_wu_vec.size() << " non-tried cubes and " << wu_vec.size() << " cubes in total." << endl;
		cout << "first cubes : " << endl;
		unsigned maxprint = nontried_wu_vec.size() >= 3 ? 3 : nontried_wu_vec.size(); 
		for (unsigned i = 0; i < maxprint; i++) nontried_wu_vec[i].print();
		unsigned sat_cubes = 0;
		unsigned unsat_cubes = 0;
		unsigned interr_cubes = 0;
		unsigned skipped_cubes = 0;
		size_t wus_num = wu_vec.size();
		size_t nontried_wus_num = nontried_wu_vec.size();
		assert(nontried_wus_num <= wus_num);
		bool is_add_sat_clause = false;
		// Process all workunits in parallel:
		#pragma omp parallel for schedule(dynamic, 1)
		for (auto &wu : nontried_wu_vec) {
			// Skip a cube because SAT is found:
			if (sat_cubes) {
				skipped_cubes++;
				continue;
			}
			result res = solve_cube(base_cnf_name, cur_cnf, cdcl_solver_name,
				program_start, wu, cube_conflict_lim);
			if (res == SAT) {
				sat_cubes++;
				cout << "SAT is found." << endl;
				print_stats(wu, sat_cubes, unsat_cubes, interr_cubes);
				// Kill the solver once if the SAT finding mode:
				cout << "Killing CDCL solver " << cdcl_solver_name << endl;
				kill_solver(cdcl_solver_name);
			}
			else if (res == UNSAT) {
				unsat_cubes++;
				print_stats(wu, sat_cubes, unsat_cubes, interr_cubes);
			}
			else {
				// A CDCL solver was interrupted due to a time limit:
				interr_cubes++;
				assert(res == INTERR);
				string cube_str = cube_to_str(wu.cube);
				// If a cube not in the set, add it:
				cout << cube_str << endl;
				// An already processed cube must be excluded from the current list:
				assert(interr_cubes_set.find(cube_str) == interr_cubes_set.end());
				interr_cubes_set.insert(cube_str);
				//else {
				//	cout << "Already interrupted cube : " << cube_str << endl;
				//}
				print_stats(wu, sat_cubes, unsat_cubes, interr_cubes);
			}
			// If all but one solved and UNSAT, interrupt the remaining one:
			if (unsat_cubes == wus_num-1 and sat_cubes == 0 and interr_cubes == 0) {
				is_add_sat_clause = true;
				// Interrupt processing of the last cube: 
				cout << "Interrupt the only unprocessed cube by killing CDCL solver " << cdcl_solver_name << endl;
				kill_solver(cdcl_solver_name);
			}
		}
		cout << "skipped-cubes : " << skipped_cubes << endl;

		cout << "Result : ";
		// If at least one cube-problem is SAT, return SAT:
		if (sat_cubes) {
			assert(unsat_cubes < nontried_wus_num);
			assert(interr_cubes < nontried_wus_num);
			assert(skipped_cubes + sat_cubes + unsat_cubes + interr_cubes == nontried_wus_num);
			cout << "SAT" << endl;
			break;
		}
		// If all (generated) cube-problems are UNSAT, return UNSAT: 
		else if (unsat_cubes == wus_num) {
			assert(sat_cubes == 0);
			assert(interr_cubes == 0);
			cout << "UNSAT" << endl;
			break;
		}
		// If all (previously non-interrupted) cube-problems are interrupted, return INTERRUPTED
		// since no negation-clauses are added to a CNF:
		else if (interr_cubes == nontried_wus_num) {
			assert(sat_cubes == 0);
			assert(unsat_cubes == 0);
			cout << "INTERRUPTED" << endl;
			break;
		}
		// If at least one cube-problem is UNSAT and at least one cube-problem
		// is interrupted:
		else if (not is_add_sat_clause and unsat_cubes > 0) {
			assert(unsat_cubes <= nontried_wus_num);
			assert(sat_cubes == 0);
			assert(skipped_cubes == 0);
			assert(unsat_cubes + interr_cubes == nontried_wus_num);
			// Make a new cnf where negation-clauses are added for unsat cubes:
			cnf new_cnf = add_sat_unsat_clauses(cur_cnf, nontried_wu_vec, iter_num);
			cout << "new iteration on CNF " << new_cnf.name << endl;
			cur_cnf = new_cnf;
		}
		// If all but one cube-problem are UNSAT and the remaining one is not
		// solved yet:
		else if (unsat_cubes == wus_num-1) {
			assert(is_add_sat_clause == true);
			assert(sat_cubes == 0);
			assert(skipped_cubes == 0);
			assert(interr_cubes == 1);
			// Make a new cnf where negation-clauses are added to unsat-cubes,
			// while the remaining cube is added as unit clauses:
			cnf new_cnf = add_sat_unsat_clauses(cur_cnf, nontried_wu_vec, iter_num, true);
			cout << "new iteration on CNF " << new_cnf.name << endl;
			cur_cnf = new_cnf;
		}
		iter_num++;
		print_elapsed_time(program_start);
		cout << endl;
	}

	cout << interr_cubes_set.size() << " interrupted cubes in set" << endl;
	cout << "Writing interrupted cubes to file interrupted_cubes" << endl;
	ofstream ofile("interrupted_cubes_" + base_cnf_name, ios_base::out);
	for (auto x : interr_cubes_set) {
		for (auto y : x) {
			if (y == '+') ofile << " ";
			else ofile << y;
		}
		ofile << " 0" << endl;
	}
	ofile.close();
	print_elapsed_time(program_start);

    return 0;
}

// For a given number of threads n, find a cutoff threshold that gives at most
// n cubes:
unsigned get_cutoff(const string la_solver_name,
					const cnf cur_cnf,
	                const unsigned prev_threshold,
					const unsigned nthreads,
					set<string> interr_cubes_set) {
	assert(cur_cnf.name != "");
	assert(cur_cnf.var_num > 0);
	const string cnf_name = cur_cnf.name;
	unsigned cur_threshold = prev_threshold;
	if (cur_threshold == 0) {
		cur_threshold = get_free_vars(la_solver_name, cur_cnf);
	}
	assert(cur_threshold > 0);
	cout << "Start searching for threshold from " << cur_threshold << endl;

	string cubes_name = "cubes";
	unsigned cubes_num = 0;
	set<unsigned> tried_thresholds;
	for (;;) {
		// Erase the file with cubes since when interrupted lookahead does not write to it:
		ofstream ofile(cubes_name, ios_base::out | ios_base::trunc);
		ofile.close();
		//
		string system_str = "timeout 10 " + la_solver_name + " " + cnf_name + " -n " + to_string(cur_threshold) + " -o " + cubes_name;
		tried_thresholds.insert(cur_threshold);
		exec(system_str);
		bool is_interrupted_la = is_empty_file(cubes_name);

		vector<workunit> wu_vec = read_cubes(cubes_name);
		unsigned all_cubes_num = wu_vec.size();
		vector<workunit> nontried_wu_vec;
		for (auto &wu : wu_vec) {
			string cube_str = cube_to_str(wu.cube);
			if (interr_cubes_set.find(cube_str) == interr_cubes_set.end()) {
				nontried_wu_vec.push_back(wu);
			}
		}
		if (all_cubes_num == 0) {
			cout << "No cubes where found in the call : " << endl << system_str << endl;
		}

		cubes_num = nontried_wu_vec.size();
		cout << cubes_num << " non-tried cubes out of " << all_cubes_num << " on n " << cur_threshold << endl;

		// If lookahead was interrupted due to the time limit:
		if (is_interrupted_la) {
			assert(all_cubes_num == 0 and cubes_num == 0);
			// Go back to the last acceptable threshold:
			cur_threshold++;
		}
		else if ((cubes_num >= 0) and (cubes_num < nthreads)) {
			// If a decreased threshold has already been tried, break:
			if (tried_thresholds.find(cur_threshold-1) != tried_thresholds.end()) {
				cout << "Don't try threshold " << cur_threshold-1 << " since it has already been tried." << endl;
				break;
			}
			// Decrease the threshold to get more cubes:
			cur_threshold--;
		}
		// Exectly the required number of cubes:
		else if (cubes_num == nthreads) {
			break;
		}
		else if (cubes_num > nthreads) {
			assert(is_interrupted_la == false);
			// If an increased threshold has already been tried, break:
			if (tried_thresholds.find(cur_threshold+1) != tried_thresholds.end()) {
				cout << "Choose threshold " << cur_threshold+1 << " since it the last one gave less than threshold." << endl;
				cur_threshold++;
				break;
			}
			// Go back to the last acceptable threshold (cubes_num < nthreads):
			cur_threshold++;
		}
	}

	return cur_threshold;
}

// Run lookahead solver and parse the number of free variables from its output:
unsigned get_free_vars(const string la_solver_name, const cnf cur_cnf) {
	assert(cur_cnf.name != "");
	assert(cur_cnf.var_num > 0);
	string system_str = la_solver_name + " " + cur_cnf.name + " -n " +
	                    to_string(cur_cnf.var_num);
	string res_str = exec(system_str);
	stringstream res_sstream(res_str);
	string str;
	while (getline(res_sstream, str)) {
		if (str.find("free variables") != string::npos) {
			stringstream sstream(str);
			string word;
			vector<string> words;
			while (sstream >> word) words.push_back(word);
			assert(words.size() == 7);
			return stoi(words[6]);
		}
	}
	return 0;
}

string exec(const string cmd_str) {
	char* cmd = new char[cmd_str.size() + 1];
	for (unsigned i = 0; i < cmd_str.size(); i++)
		cmd[i] = cmd_str[i];
	cmd[cmd_str.size()] = '\0';
	FILE* pipe = popen(cmd, "r");
	delete[] cmd;
	if (!pipe) return "ERROR";
	char buffer[128];
	string result = "";
	while (!feof(pipe)) {
		if (fgets(buffer, 128, pipe) != NULL)
			result += buffer;
	}
	pclose(pipe);
	return result;
}

// Read cubes from a given file
vector<workunit> read_cubes(const string cubes_name) {
	vector<workunit> wu_cubes;
	ifstream cubes_file(cubes_name);
	if (!cubes_file.is_open()) {
		cerr << "cubes_file " << cubes_name << " wasn't opened" << endl;
		exit(EXIT_FAILURE);
	}
	
	string str;
	stringstream sstream;
	vector<workunit> wu_vec;
	int id = 0;
	while (getline(cubes_file, str)) {
		sstream << str;
		string word;
		cube_t cube;
		while (sstream >> word) {
			if (word == "a" or word == "0") continue;
			cube.push_back(stoi(word));
		}
		// If there is no cube in the string, skip it:
		if (cube.size() == 0) continue;
		sort(cube.begin(), cube.end());
		workunit wu;
		assert(wu.id == -1);
		assert(wu.stts == NOT_STARTED);
		assert(wu.rslt == INTERR);
		assert(wu.time == -1);
		wu.cube = cube;
		sstream.str(""); sstream.clear();
		wu.id = id++;
		wu_vec.push_back(wu);
	}
	cubes_file.close();
	return wu_vec;
}

// Check if a text file is empty:
bool is_empty_file(const string fname) {
	ifstream ifile(fname);
	if (!ifile.is_open()) {
		cerr << "file " << fname << " wasn't opened" << endl;
		exit(EXIT_FAILURE);
	}
	
	string str;
	stringstream sstream;
	vector<workunit> wu_vec;
	int id = 0;
	while (getline(ifile, str)) {
		if (str != "") return false;
	}
	ifile.close();
	return true;
}

result solve_cube(const string base_cnf_name, const cnf c,
				  const string solver_name, const time_point_t program_start,
				  workunit &wu, const unsigned cube_conflict_lim)
{
	string wu_id_str = to_string(wu.id);
	string local_cnf_file_name = "id-" + wu_id_str + "-cnf";

	ofstream local_cnf_file(local_cnf_file_name, ios_base::out);
	local_cnf_file << "p cnf " << c.var_num << " "
	               << c.clause_num + wu.cube.size() << endl;
	for (auto cl : c.clauses) local_cnf_file << cl << endl;
	for (auto x : wu.cube) local_cnf_file << x << " 0" << endl;
	local_cnf_file.close();

	string system_str = solver_name + " --conflicts=" +
	  to_string(cube_conflict_lim) + " " + local_cnf_file_name;
	//cout << system_str << endl;
	string local_out_file_name = "id-" + wu_id_str + "-out";
	fstream local_out_file;
	local_out_file.open(local_out_file_name, ios_base::out);

	const time_point_t solver_start = chrono::system_clock::now();
	string res_str = exec(system_str);
	const time_point_t solver_end = chrono::system_clock::now();
	const double solver_time = chrono::duration_cast<chrono::milliseconds>(solver_end - solver_start).count() / (double)1000;
	wu.time = solver_time;

	local_out_file << res_str;
	local_out_file.close(); local_out_file.clear();

	result res = read_solver_result(local_out_file_name);
	wu.rslt = res;
	wu.stts = PROCESSED;

	// Remove temporary files:
	if (res == SAT) {
		const time_point_t program_end = chrono::system_clock::now();
		const double elapsed = chrono::duration_cast<chrono::seconds>(program_end - program_start).count();
		string fname = "!sat_" + base_cnf_name + "_info_cube_id_" + wu_id_str;
		ofstream ofile(fname, ios_base::out);
		ofile << "SAT" << endl;
		ofile << "elapsed : " << elapsed << " seconds" << endl;
		ofile << "solver time : " << wu.time << " s" << endl;
		ofile << "cube id : " << wu.id << endl;
		ofile << "cube : " << endl;
		for (auto &x : wu.cube) ofile << x << " ";
		ofile << endl;
		ofile.close();
		fname = "./!sat_" + base_cnf_name + "_out_cube_id_" + wu_id_str;
		system_str = "cp " + local_out_file_name + " " + fname;
		exec(system_str);
		fname = "./!sat_" + base_cnf_name + "_cnf_cube_id_" + wu_id_str;
		system_str = "cp " + local_cnf_file_name + " " + fname;
		exec(system_str);
	}

	system_str = "rm id-" + wu_id_str + "-*";
	exec(system_str);
	return res;
}

result read_solver_result(const string fname) {
	result res = INTERR;
	ifstream ifile(fname, ios_base::in);
	if (!ifile.is_open()) {
		cerr << "solver result file " << fname << " wasn't opened\n";
		exit(EXIT_FAILURE);
	}
	string str;
	while (getline(ifile, str)) {
		if (str.find("s SATISFIABLE") != string::npos) {
			res = SAT;
			break;
		}
		else if (str.find("s UNSATISFIABLE") != string::npos) {
			res = UNSAT;
			break;
		}
	}
	ifile.close();
	return res;
}

void print_stats(const workunit wu, const unsigned sat_cubes,
	             const unsigned unsat_cubes, const unsigned interr_cubes)
{
	cout << wu.time << " sec"
	<< "  sat-cubes : " << sat_cubes
	<< "  unsat-cubes : " << unsat_cubes
	<< "  interr-cubes : " << interr_cubes
	<< endl;
}

void kill_solver(const string solver_name) {
	string system_str = "killall -9 " + solver_name;
	exec(system_str);
}

void print_elapsed_time(const time_point_t program_start) {
	const time_point_t program_end = chrono::system_clock::now();
	cout << "Elapsed : "
	<< chrono::duration_cast<chrono::seconds>(program_end - program_start).count()
	<< " seconds" << endl;
}

// Add a negation-clause for each UNSAT cube and a unit clause for each
// literal from the only unprocessed cube (if such exists):
cnf add_sat_unsat_clauses(cnf cur_cnf, vector<workunit> wu_vec,
	                      const unsigned iter_num,
						  const bool is_add_sat_clause) {
	cnf new_cnf;
	vector<cube_t> unsat_cubes;
	vector<cube_t> inter_cubes;
	unsigned wus_num = wu_vec.size();
	for (auto &wu : wu_vec) {
		assert (wu.stts == PROCESSED);
		if (wu.rslt == UNSAT) unsat_cubes.push_back(wu.cube);
		else inter_cubes.push_back(wu.cube);
	}
	assert(not unsat_cubes.empty());
	string new_cnf_name;
	// If an original CNF name is given:
	size_t pos_iter = cur_cnf.name.find("_iter");
	if (pos_iter == string::npos) {
		size_t pos_cnf = cur_cnf.name.find(".cnf");
		assert(pos_cnf != string::npos);
		new_cnf_name = cur_cnf.name.substr(0, pos_cnf) + "_iter" +
		               to_string(iter_num) + ".cnf";
	}
	else {
		assert(pos_iter != string::npos);
		new_cnf_name = cur_cnf.name.substr(0, pos_iter) + "_iter" +
		               to_string(iter_num) + ".cnf";
	}

	// Make a new CNF file:
	ofstream ofile(new_cnf_name, ios_base::out);
	unsigned cla_num = cur_cnf.clause_num + unsat_cubes.size();
	if (is_add_sat_clause) {
		assert(inter_cubes.size() == 1 and unsat_cubes.size() == wus_num-1);
		cla_num += inter_cubes[0].size();
	}
	ofile << "p cnf " << cur_cnf.var_num << " " << cla_num << endl;
	// Add unit clauses for the only unprocessed cube if needed:
	if (is_add_sat_clause) {
		string str = "";
		for (auto &lit : inter_cubes[0]) {
			ofile << lit << " 0" << endl;
		}
	}
	// Add negation-clauses for the UNSAT cubes:
	for (auto &cube : unsat_cubes) {
		string str = "";
		for (auto &lit : cube) {
			str += to_string(-lit) + " ";
		}
		str += "0";
		ofile << str << endl;
	}
	for (auto &cla : cur_cnf.clauses) {
		ofile << cla << endl;
	}
	ofile.close();

	new_cnf.read(new_cnf_name);
	
	return new_cnf;
}
