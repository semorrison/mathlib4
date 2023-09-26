#!/bin/bash

cat $1 | ./mk_lean.py | zsh -c 'time lake -d=../../../.. env lean --stdin > /dev/null 2>&1' 2>&1 | awk -F' ' '{print $(NF-1)}'
