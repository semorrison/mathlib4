#!/usr/bin/env python3

# https://chat.openai.com/share/40c7edfb-4bb2-47bd-a63a-5318544b1f04

import subprocess
import numpy as np
from scipy.optimize import curve_fit
import sys

def run_cmd(cmd, n):
    """Run the external command with n as the last argument and return its output as a float."""
    result = subprocess.run(cmd + [str(n)], capture_output=True, text=True)
    return float(result.stdout.strip())

def linear(x, a, b):
    return a * x + b

def quadratic(x, a, b, c):
    return a * x**2 + b * x + c

def exponential_log(x, ln_a, b):
    return ln_a + b * x

def r_squared(y, y_pred):
    ss_res = np.sum((y - y_pred)**2)
    ss_tot = np.sum((y - np.mean(y))**2)
    return 1 - (ss_res / ss_tot)

if len(sys.argv) < 3:
    print("Usage: ./benchmark.py N cmd [args...]")
    sys.exit(1)

N = float(sys.argv[1])
cmd = sys.argv[2:]

results = []
n = 1
while len(results) < 5 or results[-1][1] <= N:
    result = run_cmd(cmd, n)
    print(f"{n}: {result}")
    results.append((n, result))

    if results[-1][1] <= N:
        n *= 2
    else:
        n += 1

x_data = np.array([x[0] for x in results])
y_data = np.array([x[1] for x in results])

# Linear
popt_linear, _ = curve_fit(linear, x_data, y_data)
linear_pred = linear(x_data, *popt_linear)
r2_linear = r_squared(y_data, linear_pred)

# Quadratic
popt_quadratic, _ = curve_fit(quadratic, x_data, y_data)
quadratic_pred = quadratic(x_data, *popt_quadratic)
r2_quadratic = r_squared(y_data, quadratic_pred)

# Exponential
y_data_log = np.log(y_data)
popt_exponential_log, _ = curve_fit(exponential_log, x_data, y_data_log)
a = np.exp(popt_exponential_log[0])
b = popt_exponential_log[1]
exp_pred = a * np.exp(b * x_data)
r2_exponential = r_squared(y_data, exp_pred)

print(f"Linear fit: Parameters: a={popt_linear[0]:.5f}, b={popt_linear[1]:.5f}. R^2: {r2_linear:.5f}")
print(f"Quadratic fit: Parameters: a={popt_quadratic[0]:.5f}, b={popt_quadratic[1]:.5f}, c={popt_quadratic[2]:.5f}. R^2: {r2_quadratic:.5f}")
print(f"Exponential fit: Parameters: a={a:.5f}, b={b:.5f}. R^2: {r2_exponential:.5f}")
