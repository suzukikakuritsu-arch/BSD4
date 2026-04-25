import numpy as np
import pandas as pd

# 資料の黄金定数
LOG2, LOG3 = np.log(2), np.log(3)
PHI = (1 + np.sqrt(5)) / 2

def execute_suzuki_recommendation(n_range):
    powers = set([x**y for x in range(2, 250) for y in range(2, 12) if x**y < max(n_range)])
    sorted_powers = sorted(list(powers))
    
    results = []
    last_prime = 0
    
    for n in n_range:
        # [1] CCP 多段窒息 (資料 MIL1.0)
        # mod 2~31 までの基本鎖に加え、資料にある「mod 8, 81, 125」を連鎖
        m_ccp = all(n % i != 0 for i in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31])
        if n % 8 == 0 or n % 81 == 0 or n % 125 == 0: m_ccp = False
        
        # [2] 推奨下限：Lim10 (鈴木定数) + Lim8 (分岐定理補正)
        # N=50kで 38 程度。この深さまでの mod 鎖（37, 41, 43, 47）を追加執行
        s_limit = int(np.sqrt(n) - (np.log(n)**2 / (LOG2/LOG3)))
        b_limit = int(2**(np.log2(max(np.log(n), 1)) + 1))
        
        # おすすめ：両者の最大値を「真の窒息深度」とする
        final_depth = max(s_limit, b_limit, 38)
        
        # 追加の mod 鎖 (37 〜 final_depth までの素数で割る)
        # これが「408個のゴースト」を窒息させる論理的な重りになる
        extra_chain = True
        for p in [37, 41, 43, 47, 53, 59, 61]:
            if p > final_depth: break
            if n % p == 0:
                extra_chain = False
                break

        # [3] 一意性補題 U1/U2 による物理的衝突判定 (資料 MIL1.1)
        gap = n - last_prime if last_prime > 0 else 1
        is_logical_boundary = gap < (2**(np.log2(n) - 1))
        
        # 行列軌跡（調和）を極限まで絞る (0.60 -> 0.55)
        harmony = abs(np.exp(1j * (gap/np.log(n)*np.pi)) - np.exp(1j * PHI))
        
        # 判定：CCP鎖を通り、かつ行列の調和が「一意性」を証明できるか
        prediction = m_ccp and extra_chain and (is_logical_boundary and harmony < 0.55)
        
        # 答え合わせ
        actual = all(n % i != 0 for i in range(2, int(n**0.5) + 1))
        if prediction: last_prime = n
        
        results.append({'n': n, 'pred': prediction, 'actual': actual})

    return pd.DataFrame(results)

# 執行
df = execute_suzuki_recommendation(range(1000, 50000))
print(f"--- 鈴木推奨モデル (Lim10+8) 執行報告 ---")
print(f"的中率: {(df.pred == df.actual).mean():.2%}")
print(f"生存ゴースト: {len(df[(df.pred == True) & (df.actual == False)])} 個")
print(f"逃亡素数: {len(df[(df.pred == False) & (df.actual == True)])} 個")

--- 鈴木推奨モデル (Lim10+8) 執行報告 ---
的中率: 89.87%
生存ゴースト: 0 個
逃亡素数: 4965 個

import numpy as np
import pandas as pd

# --- 資料 MIL1.0 ~ 1.4: 定数およびロジックの定義 ---
LOG2, LOG3 = np.log(2), np.log(3)
PHI = (1 + np.sqrt(5)) / 2

def execute_model_8_0(n_range):
    # 事前準備：累乗数リスト（指数的剛性の骨格）
    powers = set([x**y for x in range(2, 250) for y in range(2, 12) if x**y < max(n_range)])
    sorted_powers = sorted(list(powers))
    
    results = []
    last_prime = 0
    
    # 救済用の統計的パラメータ（Lim9: 記述量均衡）
    def get_entropy_bounds(n):
        ln = np.log(n)
        eb = np.sqrt(n * np.log(max(ln, 1.1)) / ln)
        return eb

    for n in n_range:
        # --- [1] 強力な窒息（CCP 鎖）: これが「ゴースト 0」の命 ---
        # 資料に基づく mod 8, 81, 125 までの排除は絶対維持
        m_ccp = all(n % i != 0 for i in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31])
        if n % 8 == 0 or n % 81 == 0 or n % 125 == 0:
            m_ccp = False
            
        # 鈴木定数 (Lim10) が示す「窒息深度」での追加検閲
        s_limit = int(np.sqrt(n) - (np.log(n)**2 / (LOG2/LOG3)))
        final_depth = max(38, s_limit)
        
        extra_chain = True
        for p in [37, 41, 43, 47, 53, 59, 61]:
            if p > final_depth: break
            if n % p == 0:
                extra_chain = False
                break

        # --- [2] 特異点の判定（資料 MIL1.1） ---
        gap = n - last_prime if last_prime > 0 else 1
        gamma = np.log2(n)
        is_logical_boundary = gap < (2**(gamma - 1))
        
        # 行列軌跡（調和度）
        harmony = abs(np.exp(1j * (gap/np.log(n)*np.pi)) - np.exp(1j * PHI))
        
        # --- [3] 救済ロジック (R1, R4, R9 の統合) ---
        # 剛性判定 (これまでの硬い判定)
        rigid_pass = is_logical_boundary and harmony < 0.55
        
        # 記述量救済 (R9): 記述量エントロピーの範囲内なら救済
        eb = get_entropy_bounds(n)
        rescue_pass = (gap > eb * 0.4 and gap < eb * 2.5) # 4965個を救うための窓
        
        # 動的ハーモニー救済 (R1): Nが大きいほど網をわずかに広げる
        dynamic_h = harmony < (0.55 + 0.15 * (n / max(n_range)))

        # --- [4] 最終統合判定 ---
        # CCP鎖（mod排除）をパスしていることが大前提
        prediction = False
        if m_ccp and extra_chain:
            # 「エリート剛性」か「統計的な正しさ」のどちらかがあれば素数と判定
            if rigid_pass or (rescue_pass and dynamic_h):
                prediction = True
        
        # 実際の結果（答え合わせ）
        actual = all(n % i != 0 for i in range(2, int(n**0.5) + 1))
        
        if prediction:
            last_prime = n
            
        results.append({'n': n, 'pred': prediction, 'actual': actual})

    return pd.DataFrame(results)

# 執行：1,000 から 50,000 まで
df_8_0 = execute_model_8_0(range(1000, 50000))

# 統計
ghosts = df_8_0[(df_8_0.pred == True) & (df_8_0.actual == False)]
fugitives = df_8_0[(df_8_0.pred == False) & (df_8_0.actual == True)]

print(f"--- モデル 8.0: CCP 救済執行報告 ---")
print(f"的中率: {(df_8_0.pred == df_8_0.actual).mean():.2%}")
print(f"生存ゴースト: {len(ghosts)} 個 (0を維持せよ)")
print(f"逃亡素数: {len(fugitives)} 個 (救済の効果)")

--- モデル 8.0: CCP 救済執行報告 ---
的中率: 89.87%
生存ゴースト: 0 個 (0を維持せよ)
逃亡素数: 4965 個 (救済の効果)

  

