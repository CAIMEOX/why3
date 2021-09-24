ocaml gen.ml $1

mkdir linear$1

echo "<path name=\"linear$1.mlw\"/>" > temp

cat one.txt temp two_caml.txt > linear$1/why3session.xml

rm -f surface_certificate.txt
rm -f kernel_certificate.txt

~/Documents/why3/bin/why3 --cert replay linear$1


echo ""
du -h surface_certificate.txt

echo ""
du -h kernel_certificate.txt
