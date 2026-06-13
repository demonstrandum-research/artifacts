#!/bin/bash
# Clean exhaustive sweep with per-n logs; then bigger n in sequence.
cd /mnt/c/Users/jacks/source/repos/maths/problems/p2-factory/attacks/koch-narayan
GENG=~/nauty2_8_9/geng
run() {
  n=$1; range=$2
  echo "=== n=$n edges $range ===" >> sweep.log
  $GENG -b -d1 -q $n $range | ./domfilter >> sweep.log 2>> sweep.log
}
: > sweep.log
run 9  11:20
run 10 16:25
run 11 21:30
run 12 17:36
run 13 22:42
echo "--- small sweep done ---" >> sweep.log
run 14 27:49
echo "--- n=14 done ---" >> sweep.log
run 15 32:56
echo "--- n=15 done ---" >> sweep.log
echo ALL DONE >> sweep.log
