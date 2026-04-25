import numpy as np
import matplotlib.pyplot as plt
from sympy import isprime, nextprime
import math

# 1. 楕円曲線の点数カウント関数
def count_points(A, B, p):
    """ y^2 = x^3 + Ax + B over Fp の点数を数える """
    count = 1  # 無限遠点
    # x^3 + Ax + B の値を事前に計算
    rhs_table = [(x**3 + A*x + B) % p for x in range(p)]
    # 平方剰余のテーブル
    squares = [False] * p
    for y in range(p):
        squares[(y*y) % p] = True
    
    # y^2 = rhs となる点の数を加算
    for val in rhs_table:
        if val == 0:
            count += 1
        elif squares[val]:
            count += 2
    return count

def get_ap_data(A, B, max_p=1000):
    primes = []
    p = 2
    while p < max_p:
        if isprime(p):
            primes.append(p)
        p += 1
    
    aps = []
    thetas = []
    for p in primes:
        a = p + 1 - count_points(A, B, p)
        aps.append(a)
        
        # Frobenius 固有値 alpha = sqrt(p) * e^{i theta}
        # cos(theta) = ap / (2 * sqrt(p))
        cos_theta = a / (2 * math.sqrt(p))
        # 浮動小数点の誤差修正
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
    
    # 左側：ap / sqrt(p) の分布（Sato-Tate vs CM）
    normalized_aps = [a / math.sqrt(p) for a, p in zip(aps, primes)]
    axes[i, 0].hist(normalized_aps, bins=30, color='skyblue', edgecolor='black', alpha=0.7)
    axes[i, 0].set_title(f"{label} - $a_p/\sqrt{p}$ Distribution")
    axes[i, 0].set_xlabel("$a_p/\sqrt{p}$")
    
    # 右側：theta の分布
    axes[i, 1].hist(thetas, bins=30, color='salmon', edgecolor='black', alpha=0.7)
    axes[i, 1].set_title(f"{label} - Frobenius Angle $\\theta$")
    axes[i, 1].set_xlabel("$\\theta$ (radians)")
    axes[i, 1].set_xticks([0, np.pi/4, np.pi/2, 3*np.pi/4, np.pi])
    axes[i, 1].set_xticklabels(['0', '$\pi/4$', '$\pi/2$', '$3\pi/4$', '$\pi$'])

plt.show()

# 4. 統計データの表示
print("\n--- Summary Statistics ---")
for label, (A, B) in curves.items():
    _, aps, _ = get_ap_data(A, B, max_p=500)
    super_singular = sum(1 for a in aps if a == 0)
    print(f"{label}: ap=0 (Super-singular) frequency: {super_singular}/{len(aps)} ({super_singular/len(aps)*100:.1f}%)")
