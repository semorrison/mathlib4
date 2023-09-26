#!/usr/bin/env python3

# https://chat.openai.com/share/c81601df-70d9-434f-a859-31e6a167b817

import sys

def parse_line(line):
    # Split the line into left hand side, the relation, and the coefficients
    lhs, relation, *coeffs = line.split()

    # Convert the coefficients to integers
    coeffs = [int(coeff) for coeff in coeffs]

    return lhs, relation, coeffs

def generate_lean_code(line):
    lhs, relation, coeffs = parse_line(line)

    # Construct the right hand side expression in Lean
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

    # Generate the variable declarations in Lean
    variables = " ".join([f"x{i}" for i in range(1, max_coeffs + 1)])
    var_decl = f"{{{variables} : Int}}"

    # Generate the hypotheses in Lean
    hypotheses = []
    for i, line in enumerate(lines, 1):
        lean_expr = generate_lean_code(line.strip())
        hypotheses.append(f"(h{i} : {lean_expr})")

    # Generate the complete Lean code
    hyp_str = " ".join(hypotheses)

    lean_code = (
        "import Mathlib.Tactic.Omega.tactic\n\n"
        f"example {var_decl} {hyp_str} : False := by\n  omega"
    )

    print(lean_code)

if __name__ == "__main__":
    main()
