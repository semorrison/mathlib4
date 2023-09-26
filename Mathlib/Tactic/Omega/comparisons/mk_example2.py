#!/usr/bin/env python3

import sys

def generate_pattern(n):
    if n < 2:
        print("Please enter a value of n greater than or equal to 2")
        return

    # Print the initial part of the pattern
    print("-1 ≤ 2")
    print("0 = 1 -1")

    if n == 2:
        return

    # Print the middle part of the pattern
    for i in range(1, n - 1):
        line = "0 = " + "0 " * i + "1 -1"
        print(line)

    # Print the last part of the pattern
    last_line = "1 ≤ " + "0 " * (n - 1) + "-2"
    print(last_line)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: script_name <n>")
        sys.exit(1)

    n = int(sys.argv[1])
    generate_pattern(n)
