import Lax888481.Construction1

/-!
The numbering of Construction 1's machines.

The edge selection machines are numbered by the position of their colour pair in the
enumeration of pairs by larger element then smaller, which is `b.choose 2 + a` for the
pair `{a, b}` with `a < b`. This file is the check that the numbering is what the
construction needs it to be: injective on ordered pairs and landing exactly below
`k.choose 2`, so that the validation machine at `k.choose 2` is distinct from all of
them and the machine count is the paper's `C(k,2) + 1`.
-/

namespace Lax888481Proofs.Construction1Index

open Lax888481.Construction1

/-- Pascal's rule at the top: one more element adds `b` pairs. -/
lemma choose_two_succ (b : ℕ) : (b + 1).choose 2 = b.choose 2 + b := by
  have h : (b + 1).choose 2 = b.choose 1 + b.choose 2 := Nat.choose_succ_succ b 1
  rw [Nat.choose_one_right] at h
  omega

/-- An ordered pair of colours gets a machine below `k.choose 2`. -/
theorem pairIdx_lt {a b k : ℕ} (hab : a < b) (hbk : b < k) : pairIdx a b < k.choose 2 := by
  have h1 : pairIdx a b < (b + 1).choose 2 := by
    rw [choose_two_succ]
    simp only [pairIdx]
    omega
  exact lt_of_lt_of_le h1 (Nat.choose_le_choose 2 hbk)

/-- Distinct ordered pairs of colours get distinct machines. -/
theorem pairIdx_inj {a b a' b' : ℕ} (hab : a < b) (hab' : a' < b')
    (h : pairIdx a b = pairIdx a' b') : a = a' ∧ b = b' := by
  have key : ∀ p q r s : ℕ, p < q → r < s → q < s → pairIdx p q ≠ pairIdx r s := by
    intro p q r s hpq hrs hqs
    have h1 : pairIdx p q < (q + 1).choose 2 := by
      rw [choose_two_succ]; simp only [pairIdx]; omega
    have h2 : (q + 1).choose 2 ≤ s.choose 2 := Nat.choose_le_choose 2 hqs
    have h3 : s.choose 2 ≤ pairIdx r s := by simp only [pairIdx]; omega
    omega
  rcases lt_trichotomy b b' with hb | hb | hb
  · exact absurd h (key a b a' b' hab hab' hb)
  · subst hb
    refine ⟨?_, rfl⟩
    simp only [pairIdx] at h
    omega
  · exact absurd h.symm (key a' b' a b hab' hab hb)

/--
---
conclusion: Lax888481.Construction1.machines_eq
---
The machines are the `C(k,2)` edge selection machines, numbered by their colour pair,
together with the validation machine numbered `C(k,2)`; `pairIdx_lt` and
`pairIdx_inj` are what say that numbering uses each of the first `C(k,2)` numbers exactly
once.
-/
theorem machines_eq (G : Lax888481.MulticolouredClique.Instance) :
    (inst G).machines = G.colours.choose 2 + 1 := rfl

end Lax888481Proofs.Construction1Index
