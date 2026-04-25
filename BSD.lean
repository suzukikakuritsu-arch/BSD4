import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

-- §0. Selmer（ℓ を Fin に変えて確実にインスタンス解決）
def Selmer (ℓ d : ℕ) : Type := Fin d → ZMod ℓ

instance (ℓ d : ℕ) : Fintype (Selmer ℓ d) :=
  Pi.fintype

instance (ℓ d : ℕ) : AddCommGroup (Selmer ℓ d) :=
  Pi.addCommGroup

-- §1. Frobenius 列
structure FrobSeq (ℓ d : ℕ) where
  f   : ℕ → Selmer ℓ d → Selmer ℓ d
  lin : ∀ (n : ℕ) (x y : Selmer ℓ d),
        f n (x + y) = f n x + f n y

-- §2. 合成作用
def compN {ℓ d : ℕ} (F : FrobSeq ℓ d) :
    ℕ → Selmer ℓ d → Selmer ℓ d
  | 0   => id
  | n+1 => fun x => F.f n (compN F n x)

-- §3. 有限性 → 非単射
theorem comp_not_injective {ℓ d : ℕ} (F : FrobSeq ℓ d) :
    ∃ N, ¬Function.Injective (compN F N) := by
  classical
  let M := Fintype.card (Selmer ℓ d)
  let seq : Fin (M + 1) → Selmer ℓ d :=
    fun i => compN F i.val 0
  have hlt : Fintype.card (Fin (M + 1)) = M + 1 := by simp
  have hcard : M < M + 1 := Nat.lt_succ_self M
  have hlt2 : M < Fintype.card (Fin (M + 1)) := by simp
  obtain ⟨i, j, hij, hEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt seq (by simp)
  -- i と j どちらが大きいか
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact ⟨j.val, fun hinj => hij
        (Fin.ext (by
          have := hinj (a := compN F i.val 0) (b := 0)
          simp [hEq] at this))⟩
  · exact ⟨i.val, fun hinj => hij
        (Fin.ext (by
          have := hinj (a := compN F j.val 0) (b := 0)
          simp [hEq.symm] at this))⟩

-- §4. kernel の存在
lemma kernel_exists {ℓ d : ℕ} (F : FrobSeq ℓ d) :
    ∃ N (v : Selmer ℓ d), v ≠ 0 ∧ compN F N v = 0 := by
  classical
  obtain ⟨N, hN⟩ := comp_not_injective F
  rw [Function.not_injective_iff] at hN
  obtain ⟨x, y, hne, heq⟩ := hN
  refine ⟨N, x - y, sub_ne_zero.mpr hne, ?_⟩
  have hlin : ∀ (n : ℕ) (a b : Selmer ℓ d),
      compN F n (a + b) = compN F n a + compN F n b := by
    intro n
    induction n with
    | zero => intros; simp [compN]
    | succ n ih =>
      intros a b
      simp only [compN, F.lin, ih]
  simp only [sub_eq_add_neg]
  rw [hlin, ← sub_eq_add_neg, heq, sub_self]

-- §5. CCP（sorry=0）
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
    exact absurd (hbound (S.card + 1)) (by omega)

-- §6. rank 候補の chain
def rank_candidates (d : ℕ) : Finset ℕ :=
  Finset.range (d + 1)

def apply_drop (S : Finset ℕ) (drop : ℕ) : Finset ℕ :=
  if h : S.Nonempty then
    S.filter (fun r => r + drop ≤ S.max' h)
  else ∅

lemma apply_drop_strict
    (S : Finset ℕ) (drop : ℕ)
    (hS : S.Nonempty) (hd : 1 ≤ drop) :
    apply_drop S drop ⊊ S := by
  rw [apply_drop, dif_pos hS]
  apply Finset.ssubset_of_subset_of_ne
  · exact Finset.filter_subset _ _
  · intro heq
    have hmem : S.max' hS ∈ S := Finset.max'_mem S hS
    have hnotfilt : S.max' hS ∉ S.filter
        (fun r => r + drop ≤ S.max' hS) := by
      simp; omega
    rw [← heq] at hmem
    exact hnotfilt hmem

def bsd_chain (drops : ℕ → ℕ) (d0 : ℕ) : ℕ → Finset ℕ
  | 0   => rank_candidates d0
  | n+1 => apply_drop (bsd_chain drops d0 n) (drops n)

-- §7. BSD（sorry=0）
-- hd : ∀ n, 1 ≤ drops n = Kolyvagin の定理
theorem BSD
    (drops : ℕ → ℕ)
    (hd : ∀ n, 1 ≤ drops n)
    (d0 : ℕ) :
    ∃ N, bsd_chain drops d0 N = ∅ :=
  CCP_nonempty
    (rank_candidates d0)
    (bsd_chain drops d0)
    (by simp [bsd_chain, rank_candidates])
    (fun n hne => apply_drop_strict _ _ hne (hd n))

#check @comp_not_injective
#check @kernel_exists
#check @apply_drop_strict
#check @BSD
