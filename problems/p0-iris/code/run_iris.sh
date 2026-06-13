#!/bin/bash
set -e
cd ~/iris_vet/plantri55
cp /mnt/c/Users/jacks/source/repos/maths/iris_vet/iris_filter.c .
gcc -O3 -march=native '-DPLUGIN="iris_filter.c"' -o plantri_iris plantri.c
echo COMPILED
for n in 8 9 10 11 12 13 14; do
  echo "=== n=$n ==="
  ./plantri_iris -a $n iris_out_$n.txt
done
echo "--- violation outputs ---"
wc -c iris_out_*.txt
cat iris_out_*.txt
