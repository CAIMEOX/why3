EX_LIB="-L examples/vacid_0_binary_heaps \
	   -L examples/avl -L examples/ring_decision \
	   -L examples/multiprecision \
	   -L examples/verifythis_2016_matrix_multiplication \
	   -L examples/prover -L examples/double_wp"

export BENCHDIR=bench-sessions

if [ -d $BENCHDIR ]; then
	if [ "$1" = "-r" ]; then
    	echo "Removing existing sessions in $BENCHDIR..."$'\n'
	rm -rf $BENCHDIR/*
	fi
else mkdir $BENCHDIR;
fi

if [ -z "$(ls -A $BENCHDIR)" ]; then
    for i in $(cd examples; find . -name "*.mlw"); do
	printf "Creating session for example $i... \n"
	SESDIR=$BENCHDIR/$(dirname $i)
	mkdir -p $SESDIR
	why3 session create $EX_LIB "examples/"$i -o $SESDIR/$(basename $i .mlw)
	why3 session update $EX_LIB --extra-config why3extra.conf --add-provers Z3,computerdiv:Z3,4.12.2 $SESDIR/$(basename $i .mlw)
    done
fi

echo "There are XXX sessions in $BENCHDIR. Running why3 bench."
for i in $(find $BENCHDIR -name why3session.xml); do
	echo "Running bench $i..."
	why3 bench $i $EX_LIB --extra-config why3extra.conf
done

# bin/why3 session create $(find examples -name "*.mlw" | head -n 100) -o bench_sessions $EX_LIB
# bin/why3 session update --add-provers Z3,computerdiv bench_sessions --extra-config why3extra.conf
# bin/why3 session update --add-provers Z3,4.12.2 bench_sessions
# bin/why3 bench bench_sessions $EX_LIB --extra-config why3extra.conf
