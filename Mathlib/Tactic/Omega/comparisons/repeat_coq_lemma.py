#!/usr/bin/env python3

# https://chat.openai.com/share/0ec23f96-4c1c-4398-92d8-56f3ecbc01d3

import sys
import re

def process_coq_file(input_text, repetitions=5):
    # Split the input text into lines
    lines = input_text.strip().split("\n")

    # Identify the start and end of the lemma block
    lemma_start = None
    lemma_end = None
    for idx, line in enumerate(lines):
        if line.startswith("Lemma "):
            lemma_start = idx
        if "Qed." in line:
            lemma_end = idx
            break

    if lemma_start is None or lemma_end is None:
        raise ValueError("Lemma block not found in the provided input.")

    # Extract the header and lemma block
    header = lines[:lemma_start]
    lemma_block = lines[lemma_start:lemma_end+1]

    # Extract the lemma name
    lemma_name = lemma_block[0].split()[1]

    # Create new lemma blocks with modified names
    new_lemmas = []
    for i in range(1, repetitions+1):
        new_lemma_name = f"{lemma_name}{i}"
        new_block = []
        for line in lemma_block:
            # Replace only if it matches at the start of the line
            new_line = re.sub(r'^Lemma ' + lemma_name, 'Lemma ' + new_lemma_name, line)
            new_block.append(new_line)
        new_lemmas.extend(new_block)

    return "\n".join(header + new_lemmas)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: ./repeat_lemma.py <number_of_repetitions>")
        sys.exit(1)
    try:
        repetitions = int(sys.argv[1])
    except ValueError:
        print("Error: The argument should be an integer.")
        sys.exit(1)

    input_text = sys.stdin.read()
    output_text = process_coq_file(input_text, repetitions)
    print(output_text)
