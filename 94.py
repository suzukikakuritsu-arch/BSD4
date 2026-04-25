import numpy as np
import matplotlib.pyplot as plt
from sympy import isprime
import math

def count_points(A, B, p):
    count = 1
    rhs_table = [(x**3 + A*x + B) % p for x in range(p)]
    squares = [False] * p
    for y in range(p):
        squares[(y*y) % p] = True
    for val in rhs_table:
        if val == 0: count += 1
        elif squares[val]: count += 2
    return count

def get_l_function_series(A, B, max_p=3000):
    primes = []
    l_values = []
    current_l = 1.0
    
    p = 2
    while p < max_p:
        if isprime(p):
            a_p = p + 1 - count_points(A, B, p)
            # Euler factor at s=1: (1 - a_p/p + 1/p)^-1
            # 簡略化のため、p|disc のケース（悪い素数）も同様に扱う
            factor = 1.0 / (1.0 - a_p/p + 1.0/p)
            current_l *= factor
            
            primes.append(p)
            l_values.append(current_l)
        p += 1
    return primes, l_values

# 曲線定義
curves = {
    'E1: rank=0 (CM)': (-1, 0),
    'E2: rank=1 (non-CM)': (-1, 1),
    'E3: rank=2 (CM)': (0, -4)
}

plt.figure(figsize=(12, 8))

for label, (A, B) in curves.items():
    print(f"Calculating L-series for {label}...")
    primes, l_values = get_l_function_series(A, B, max_p=5000)
    plt.plot(primes, l_values, label=label)

plt.axhline(0, color='black', linewidth=1, linestyle='--')
plt.title(r"Partial Euler Product of $L(E, 1)$", fontsize=15)
plt.xlabel("Number of primes (p)", fontsize=12)
plt.ylabel(r"$\prod_{p<N} (1 - a_p/p + p^{-1})^{-1}$", fontsize=12)
plt.legend()
plt.grid(True, which='both', linestyle=':', alpha=0.5)
plt.yscale('log') # 値の差が大きいためログスケールを推奨
plt.show()
