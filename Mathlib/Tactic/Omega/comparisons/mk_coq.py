#!/usr/bin/env python3

# https://chat.openai.com/share/c81601df-70d9-434f-a859-31e6a167b817

import sys

def parse_line(line):
    # Split the line into left hand side, the relation, and the coefficients
    lhs, relation, *coeffs = line.split()

    # Convert the coefficients to integers
    coeffs = [int(coeff) for coeff in coeffs]

    return lhs, relation, coeffs

def generate_coq_code(line):
    lhs, relation, coeffs = parse_line(line)

    # Replace the "≤" symbol with "<="
    if relation == "≤":
        relation = "<="

    # Construct the right hand side expression in Coq
    terms = []
    for i, coeff in enumerate(coeffs, 1):
        if coeff != 0:  # Exclude terms with zero coefficients
            terms.append(f"{coeff}*x{i}")

    rhs = " + ".join(terms)

    return f"{lhs} {relation} {rhs}"

def main():
    # Read the input lines
    lines = sys.stdin.readlines()

    # Find the maximum number of coefficients in any constraint
    max_coeffs = max(len(parse_line(line)[2]) for line in lines)

    # Generate the variable declarations in Coq
    variables = ", ".join([f"forall x{i}: Z" for i in range(1, max_coeffs + 1)])

    # Generate the hypotheses in Coq
    hypotheses = [generate_coq_code(line.strip()) for line in lines]
    hyp_str = " /\\ ".join(hypotheses)

    coq_code = (
        "From Coq Require Import ZArith.\n"
        "Require Import Lia.\n\n"
        "Open Scope Z_scope.\n\n"
        f"Lemma example : {variables}, {hyp_str} -> False.\n"
        "  lia.\n"
        "Qed.\n"
    )

    print(coq_code)

if __name__ == "__main__":
    main()
