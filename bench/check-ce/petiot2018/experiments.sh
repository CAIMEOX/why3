#!/usr/bin/env bash
set -Eeuo pipefail

# Replicate the experiments by Petiot (2018) using RAC execution of CEs.

PROVER="Z3,4.8.4"
PROVERCE="Z3,4.8.4,counterexamples"
PROVERRAC="Z3,4.8.4"

why3="bin/why3"
outbase="$(dirname $0)"
libdir="$(dirname $0)"
expdir="$libdir/experiments"
only=""

while [ $# != 0 ]; do
    case "$1" in
        "--why3")
            why3="$2"
            shift 1 ;;
        "--only")
            only="$2"
            shift 1 ;;
        "--help" | "-h" | *)
            echo "Usage: $(basename $0) [--why3 <why3-binary>] [--only <experiment>]"
            exit ;;
    esac
    shift
done

really () {
    [ -z "$only" -o "$only" = "$1" ]
}

# Clean experiment output
clean () {
    sed 's/ ([0-9.]\+s, [0-9]\+ steps)\././'
}

# Run why3 prove with CE checking on sub-goal $1 in file $2
why3provece () {
    goal="$1"
    expfile="$2"
    command=("$why3" prove
             --library="$libdir" "$expfile"
             --apply-transform=split_vc
             --prover="$PROVERCE"
             --timelimit=15
             --check-ce --rac-prover="$PROVERRAC"
             --sub-goal="$goal")
    echo "${command[@]}" 2>&1
    "${command[@]}" 2>&1 || [ $? -eq 2 ]
}

# Run an experiment with name $1. The program modifications are read from stdin.
# Stdout and stderr of the calls to why3 goes to stdout and will be piped to
# outfiles in under $outbase/, progress goes to stderr.
experiment () {
    experiment=$1
    echo -n "Experiment $experiment:" >&2
    echo "* Experiment $experiment"
    echo "** Original"
    prove_opts=(--apply-transform=split_vc --prover="$PROVER" --library="$libdir")
    $why3 prove "${prove_opts[@]}" "$libdir/$experiment.mlw"
    while IFS=$'\t' read -r id lines mod goal; do
        echo -n " $id" >&2
        name="$experiment-$id"
        expfile="$expdir/$name.mlw"
        echo "** $name"
        sedargs=()
        for line in $lines; do
            sedargs+=(-e "$line c $mod")
        done
        sed "${sedargs[@]}" "$libdir/$experiment.mlw" > "$expfile"
        why3provece "$goal" "$expfile"
    done
    echo >&2
}

mkdir -p "$expdir"

# Input is TSV with columns: ID, Line(s), Line replacement, Goal

really isqrt && ( experiment isqrt | clean > "$outbase/isqrt.out" ) <<EOF
S1	4	(* empty *)	:10@loop invariant init
S2	8	let z = int_ref (2 * n + 1) in	:13@loop invariant init
S3	13	invariant I4 { !z = 2 * !r + 1 }	:13@loop invariant init
S4	15	y := !y - !z;	:11@loop invariant preservation
S5	13	(* empty *)	:11@loop invariant preservation
S6	9	while !y > n + 1 do	:5@postcondition
S7	12	(* empty *)	:5@postcondition
S8	19	!r - 1	:5@postcondition
S9	14	variant { !r - n }	:14@loop variant decrease
S10	10	invariant I1 { !r <= n }	:14@loop variant decrease
EOF

really binary_search && (  experiment binary_search | clean > "$outbase/binary_search.out" ) <<EOF
B1	15	variant { t.length - !r }	:15@loop variant decrease
B2	16	let m = div (!l + !r) 2 in	:15@loop variant decrease
B3	5	(* empty *)	:14@loop invariant preservation
B4	13 14	(* empty *)	:8@postcondition
EOF

really rgf && (  experiment rgf | clean > "$outbase/rgf.out"  ) <<EOF
R1	26	(* empty *)	:41@precondition
R4	40	a[!i] <- a[!i] + 2;	:41@precondition
EOF

git diff --exit-code "*.out"
