#!/bin/bash

mkdir -p tmp
cat $1 | ./mk_coq.py > tmp/bench.v
zsh -c 'time coqc tmp/bench.v' 2>&1 | awk -F' ' '{print $(NF-1)}'
rm -rf tmp
