for f in ./cbmc_*.c
do
 echo "Processing $f"
 base_name=$(basename -- "$f" .c)
 #echo $base_cnfname
 cbmc $f --dimacs --outfile ${base_name}.cnf
done
