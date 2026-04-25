import numpy as np
import matplotlib.pyplot as plt
from sympy import isprime
import math

# 1. 楕円曲線の点数カウント関数
def count_points(A, B, p):
    count = 1  # 無限遠点
    rhs_table = [(x**3 + A*x + B) % p for x in range(p)]
    squares = [False] * p
    for y in range(p):
        squares[(y*y) % p] = True
    
    for val in rhs_table:
        if val == 0:
            count += 1
        elif squares[val]:
            count += 2
    return count

def get_ap_data(A, B, max_p=1000):
    primes = []
    curr_p = 2
    while curr_p < max_p:
        if isprime(curr_p):
            primes.append(curr_p)
        curr_p += 1
    
    aps = []
    thetas = []
    for p_val in primes:
        a = p_val + 1 - count_points(A, B, p_val)
        aps.append(a)
        
        # Frobenius 角度 theta の計算
        cos_theta = a / (2 * math.sqrt(p_val))
        cos_theta = max(-1.0, min(1.0, cos_theta))
        thetas.append(math.acos(cos_theta))
        
    return primes, aps, thetas

# 2. 曲線定義
curves = {
    'E1: rank=0 (CM)': (-1, 0),
    'E2: rank=1 (non-CM)': (-1, 1),
    'E3: rank=2 (CM)': (0, -4)
}

# 3. 計算とプロット
fig, axes = plt.subplots(3, 2, figsize=(14, 15))
plt.subplots_adjust(hspace=0.4)

for i, (label, (A, B)) in enumerate(curves.items()):
    print(f"Calculating {label}...")
    primes, aps, thetas = get_ap_data(A, B, max_p=2000)
    
    # normalized_aps の計算で使う p を明示
    normalized_aps = [a / math.sqrt(p_val) for a, p_val in zip(aps, primes)]
    
    # 左側：ap / sqrt(p) の分布（r"..." で SyntaxWarning 回避）
    axes[i, 0].hist(normalized_aps, bins=30, color='skyblue', edgecolor='black', alpha=0.7)
    axes[i, 0].set_title(label + r" - $a_p/\sqrt{p}$ Distribution")
    axes[i, 0].set_xlabel(r"$a_p/\sqrt{p}$")
    
    # 右側：theta の分布
    axes[i, 1].hist(thetas, bins=30, color='salmon', edgecolor='black', alpha=0.7)
    axes[i, 1].set_title(label + r" - Frobenius Angle $\theta$")
    axes[i, 1].set_xlabel(r"$\theta$ (radians)")
    axes[i, 1].set_xticks([0, np.pi/4, np.pi/2, 3*np.pi/4, np.pi])
    axes[i, 1].set_xticklabels(['0', r'$\pi/4$', r'$\pi/2$', r'$3\pi/4$', r'$\pi$'])

plt.show()

# 4. 統計データの表示
print("\n--- Summary Statistics ---")
for label, (A, B) in curves.items():
    _, aps, _ = get_ap_data(A, B, max_p=500)
    super_singular = sum(1 for a in aps if a == 0)
    print(f"{label}: ap=0 frequency: {super_singular}/{len(aps)} ({super_singular/len(aps)*100:.1f}%)")
