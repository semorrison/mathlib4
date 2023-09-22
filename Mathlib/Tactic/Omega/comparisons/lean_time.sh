#!/bin/bash

cat $1 | ./repeat_lean_lemma.py $2 | zsh -c 'time lake -d=../../../.. env lean --stdin > /dev/null 2>1' 2>&1 | awk -F' ' '{print $(NF-1)}'
