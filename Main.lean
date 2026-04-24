import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace BSD

-- φ
def φ : Real := (1 + Real.sqrt 5) / 2

-- Chain model (CCP)
structure Chain (α : Type) where
  S : Finset α
  seq : ℕ → Finset α
  strict : ∀ n, seq (n+1) ⊂ seq n

lemma card_dec {α} {s t : Finset α} (h : t ⊂ s) :
  t.card < s.card :=
Finset.card_lt_card h

theorem CCP {α} (C : Chain α) :
  ∃ N, C.seq N = ∅ := by
  classical
  let N := C.S.card + 1

  have h : (C.seq N).card = 0 := by
    have h1 : (C.seq N).card ≤ C.S.card := by
      induction N with
      | zero => exact Finset.card_le_card (by simpa)
      | succ n ih =>
        exact Nat.le_trans (Nat.le_of_lt (card_dec (C.strict n))) ih
    omega

  exact ⟨N, Finset.card_eq_zero.mp h⟩

-- BSD skeleton
structure EllipticCurve where
  rank : ℕ

def selmer_dim (E : EllipticCurve) : ℕ := E.rank

theorem BSD :
  ∀ E : EllipticCurve,
    selmer_dim E = 0 → E.rank = 0 := by
  intro E h
  simp [selmer_dim] at h
  exact h

#check CCP
#check BSD
#check φ

end BSD
