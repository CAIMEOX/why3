for i in {26..1..-1}
do
    i1=$(($i + 1))
    sed "s/(p${i}p REP p${i1}p) REP P${i1}/P${i}/g" lin35.txt > temp
    rm -f lin35.txt
    mv temp lin35.txt
done
