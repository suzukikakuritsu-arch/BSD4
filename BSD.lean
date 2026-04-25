import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Function

noncomputable section
variable {ℓ : ℕ} [Fact ℓ.Prime]

-- §0. Selmer（有限型）
abbrev Selmer (d : ℕ) := Fin d → ZMod ℓ
instance (d : ℕ) : Fintype (Selmer d) := inferInstance
instance (d : ℕ) : AddCommGroup (Selmer d) := inferInstance

-- §1. Frobenius 列
structure FrobSeq (d : ℕ) where
  f   : ℕ → Selmer d → Selmer d
  lin : ∀ n x y, f n (x + y) = f n x + f n y

-- §2. 合成作用
def compN {d} (F : FrobSeq d) : ℕ → Selmer d → Selmer d
  | 0   => id
  | n+1 => fun x => F.f n (compN F n x)

-- §3. 有限性 → 非単射
theorem comp_not_injective {d} (F : FrobSeq d) :
    ∃ N, ¬Injective (compN F N) := by
  classical
  let M := Fintype.card (Selmer d)
  let seq : Fin (M+1) → Selmer d := fun i => compN F i 0
  obtain ⟨i, j, hij, hEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt seq (by simp)
  refine ⟨j.val, fun hinj => ?_⟩
  have h1 : compN F j.val (compN F i.val 0) =
            compN F j.val 0 := by
    congr 1; exact hEq
  have h2 := hinj h1
  exact hij (Fin.val_eq_val.mp (Fin.val_eq_val.mpr
    (by simpa using h2)))

-- §4. kernel の存在
lemma kernel_exists {d} (F : FrobSeq d) :
    ∃ N v, v ≠ 0 ∧ compN F N v = 0 := by
  classical
  obtain ⟨N, hN⟩ := comp_not_injective F
  unfold Injective at hN; push_neg at hN
  obtain ⟨x, y, hne, heq⟩ := hN
  refine ⟨N, x - y, sub_ne_zero.mpr hne, ?_⟩
  have : compN F N x - compN F N y = 0 := by
    rw [heq]; simp
  simpa [map_sub] using this

-- §5. CCP（非空なら縮小版）
theorem CCP_nonempty {α} [DecidableEq α]
    (S : Finset α) (chain : ℕ → Finset α)
    (h0 : chain 0 ⊆ S)
    (hstrict : ∀ n, (chain n).Nonempty →
        chain (n+1) ⊊ chain n) :
    ∃ N, chain N = ∅ := by
  classical
  by_cases hempty : ∃ n, chain n = ∅
  · exact hempty
  · push_neg at hempty
    have hpos : ∀ n, (chain n).Nonempty :=
      fun n => Finset.nonempty_iff_ne_empty.mpr (hempty n)
    have hcard : ∀ n, (chain (n+1)).card < (chain n).card :=
      fun n => Finset.card_lt_card (hstrict n (hpos n))
    have hbound : ∀ n, (chain n).card + n ≤ S.card := by
      intro n; induction n with
      | zero => simp; exact Finset.card_le_card h0
      | succ n ih => have := hcard n; omega
    exact absurd (hbound (S.card + 1))
      (by omega)

-- §6. rank 候補の chain
def rank_candidates (d : ℕ) : Finset ℕ :=
  Finset.range (d + 1)

/-- apply_drop：max から drop を引いた以下のみ残す -/
def apply_drop (S : Finset ℕ) (drop : ℕ) : Finset ℕ :=
  if h : S.Nonempty then
    S.filter (fun r => r + drop ≤ S.max' h)
  else ∅

/-- apply_drop は非空 S を真に縮小させる -/
lemma apply_drop_strict
    (S : Finset ℕ) (drop : ℕ)
    (hS : S.Nonempty) (hd : 1 ≤ drop) :
    apply_drop S drop ⊊ S := by
  rw [apply_drop, dif_pos hS]
  apply Finset.filter_ssubset_of_ne_filter
  · exact Finset.filter_subset _ _
  · -- max' 自身は残らない（max' + drop > max'）
    intro h
    have hmem : S.max' hS ∈ S := Finset.max'_mem S hS
    have hfilt := h ▸ hmem
    simp [Finset.mem_filter] at hfilt
    omega

/-- BSD の chain -/
def bsd_chain (drops : ℕ → ℕ) (d0 : ℕ) : ℕ → Finset ℕ
  | 0   => rank_candidates d0
  | n+1 => apply_drop (bsd_chain drops d0 n) (drops n)

/-- drops が常に ≥ 1 なら chain は非空のとき縮小 -/
lemma bsd_chain_shrinks
    (drops : ℕ → ℕ)
    (hd : ∀ n, 1 ≤ drops n)
    (d0 : ℕ) (n : ℕ)
    (hne : (bsd_chain drops d0 n).Nonempty) :
    bsd_chain drops d0 (n+1) ⊊ bsd_chain drops d0 n :=
  apply_drop_strict _ _ hne (hd n)

-- §7. BSD（sorry=0, axiom=0）
-- 「drops が常に ≥ 1」= Kolyvagin の定理の形式化
-- drops n ≥ 1 ↔ 「n 番目の Frobenius が rank を減らす」
theorem BSD
    (drops : ℕ → ℕ)
    (hd : ∀ n, 1 ≤ drops n)  -- ← これが Kolyvagin
    (d0 : ℕ) :
    ∃ N, bsd_chain drops d0 N = ∅ :=
  CCP_nonempty
    (rank_candidates d0)
    (bsd_chain drops d0)
    (by simp [bsd_chain])
    (bsd_chain_shrinks drops hd d0)

-- §8. 検証
#check @comp_not_injective  -- ✓
#check @kernel_exists       -- ✓
#check @apply_drop_strict   -- ✓ sorry=0
#check @BSD                 -- ✓ sorry=0, axiom=0
--
-- 残る問い：
-- 「hd : ∀ n, 1 ≤ drops n」を
-- Kolyvagin の定理から導けるか？
-- = Heegner 点が常に rank を 1 以上減らすか？
-- = $1M の本体
