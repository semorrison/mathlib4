#!/bin/bash

# Don't use `coqtop`, it's quadratic no matter what you're doing.
# cat $1 | ./repeat_coq_lemma.py $2 | zsh -c 'time coqtop > /dev/null 2>1' 2>&1 | awk -F' ' '{print $(NF-1)}'

mkdir -p tmp/
cat $1 | ./repeat_coq_lemma.py $2 > tmp/bench.v
zsh -c 'time coqc tmp/bench.v > /dev/null 2>&1' 2>&1 | awk -F' ' '{print $(NF-1)}'
rm -rf tmp
