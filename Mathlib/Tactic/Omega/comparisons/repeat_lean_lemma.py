#!/usr/bin/env python3

import sys

def process_lean_file(input_text, repetitions=5):
    # Split the input text into lines
    lines = input_text.strip().split("\n")

    # Identify the start of the lemma block
    lemma_start = None
    for idx, line in reversed(list(enumerate(lines))):
        if line.startswith("example "):
            lemma_start = idx
            break

    if lemma_start is None:
        raise ValueError("Lemma block not found in the provided input.")

    # Extract the header and lemma block
    header = lines[:lemma_start]
    lemma_block = lines[lemma_start:]

    # Create new lemma blocks
    new_lemmas = lemma_block * repetitions

    return "\n".join(header + new_lemmas)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: ./repeat_lean_lemma.py <number_of_repetitions>")
        sys.exit(1)
    try:
        repetitions = int(sys.argv[1])
    except ValueError:
        print("Error: The argument should be an integer.")
        sys.exit(1)

    input_text = sys.stdin.read()
    output_text = process_lean_file(input_text, repetitions)
    print(output_text)
