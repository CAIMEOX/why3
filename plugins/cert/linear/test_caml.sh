ocaml gen.ml $1

mkdir linear$1

echo "<path name=\"linear$1.mlw\"/>" > temp

cat one.txt temp two_caml.txt > linear$1/why3session.xml

~/Documents/why3/bin/why3 --cert replay linear$1


