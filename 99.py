# y² = x³ - x (rank=0) の ap を計算
# y² = x³ - x + 1 (rank=1) の ap を計算

def count_points(A, B, p):
    count = 1  # 無限遠点
    for x in range(p):
        rhs = (x**3 + A*x + B) % p
        for y in range(p):
            if (y*y) % p == rhs:
                count += 1
    return count

def ap(A, B, p):
    return p + 1 - count_points(A, B, p)
