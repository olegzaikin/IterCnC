# Generate template CNFs (without outputs)
./gen_cbmc_cnfs.sh
# Generate outputs
python3 ./gen_random_outputs.py

python3 ./add_explicit_output_vars_cbmc.py ./cbmc_skein_1r_template.cnf output
python3 ./gen_hash_preimage_instances.py ./cbmc_skein_1r_template_explicit_output.cnf ./outputs_512bit.txt 512 20

for i in {1..11}
do
    python3 ./add_explicit_output_vars_cbmc.py ./cbmc_skein_1r_${i}of12_template.cnf output
    python3 ./gen_hash_preimage_instances.py ./cbmc_skein_1r_${i}of12_template_explicit_output.cnf ./outputs_512bit.txt 512 20
done

python3 ./add_explicit_output_vars_cbmc.py ./cbmc_skein_2r_template.cnf output
python3 ./gen_hash_preimage_instances.py ./cbmc_skein_2r_template_explicit_output.cnf ./outputs_512bit.txt 512 20
