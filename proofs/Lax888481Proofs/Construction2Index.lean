import Lax888481.Construction2

/-!
The bridge between Construction 2's numbered jobs and machines and the structured names
the argument is carried out in.

An instance numbers its jobs, because a word presents them in an order, but the proof of
correctness never wants a number: it wants to say "the variable job of `v`" or "the
second wrapper of literal `h` of clause `c`". These two views are related by a pair of
bijections, set up here once, so that everything after it can be read as the paper reads.
-/

namespace Lax888481Proofs.Construction2

open Lax888481.Scheduling Lax888481.Exact34Encoding Lax888481.Construction2

variable (x : List ℕ)

/-- A job of Construction 2, named: the job of a variable, or the job in slot `s` of
literal `h` of clause `c`. Slot `0` is the literal job, `1` and `2` its two wrappers. -/
abbrev JobS : Type := Fin (nVar x) ⊕ (Fin (nCla x) × Fin 3 × Fin 3)

/-- A machine of Construction 2, named: one of the two machines of a variable — `true`
is its true machine — or one of the three machines of a clause. -/
abbrev MachS : Type := (Fin (nVar x) × Bool) ⊕ (Fin (nCla x) × Fin 3)

/-- The number of a named job. -/
def jIdx : JobS x → Fin (nJobs x)
  | .inl v => ⟨(v : ℕ), by have := v.isLt; simp only [nJobs]; omega⟩
  | .inr (c, h, s) =>
      ⟨nVar x + 9 * (c : ℕ) + 3 * (h : ℕ) + (s : ℕ), by
        have := c.isLt; have := h.isLt; have := s.isLt; simp only [nJobs]; omega⟩

/-- The number of a named machine. Machine `2v` is the true machine of variable `v` and
`2v + 1` its false machine. -/
def mIdx : MachS x → Fin (nMach x)
  | .inl (v, true) => ⟨2 * (v : ℕ), by have := v.isLt; simp only [nMach]; omega⟩
  | .inl (v, false) => ⟨2 * (v : ℕ) + 1, by have := v.isLt; simp only [nMach]; omega⟩
  | .inr (c, t) =>
      ⟨2 * nVar x + 3 * (c : ℕ) + (t : ℕ), by
        have := c.isLt; have := t.isLt; simp only [nMach]; omega⟩

lemma jIdx_injective : Function.Injective (jIdx x) := by
  rintro (v | ⟨c, h, s⟩) (v' | ⟨c', h', s'⟩) heq <;>
    simp only [jIdx, Fin.ext_iff] at heq
  · exact congrArg Sum.inl (Fin.ext heq)
  · exfalso; have := v.isLt; have := h'.isLt; have := s'.isLt; omega
  · exfalso; have := v'.isLt; have := h.isLt; have := s.isLt; omega
  · have hh := h.isLt; have hs := s.isLt; have hh' := h'.isLt; have hs' := s'.isLt
    simp only [Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff]
    omega

lemma mIdx_injective : Function.Injective (mIdx x) := by
  rintro (⟨v, b⟩ | ⟨c, t⟩) (⟨v', b'⟩ | ⟨c', t'⟩) heq
  · have hv := v.isLt; have hv' := v'.isLt
    cases b <;> cases b' <;> simp only [mIdx, Fin.ext_iff] at heq
    · exact congrArg (fun z => Sum.inl (z, false)) (Fin.ext (by omega))
    · exfalso; omega
    · exfalso; omega
    · exact congrArg (fun z => Sum.inl (z, true)) (Fin.ext (by omega))
  · exfalso
    have hv := v.isLt; have ht' := t'.isLt
    cases b <;> simp only [mIdx, Fin.ext_iff] at heq <;> omega
  · exfalso
    have hv := v'.isLt; have ht := t.isLt
    cases b' <;> simp only [mIdx, Fin.ext_iff] at heq <;> omega
  · have ht := t.isLt; have ht' := t'.isLt
    simp only [mIdx, Fin.ext_iff] at heq
    simp only [Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff]
    omega

lemma card_JobS : Fintype.card (JobS x) = Fintype.card (Fin (nJobs x)) := by
  rw [Fintype.card_fin]
  simp only [nJobs, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

lemma card_MachS : Fintype.card (MachS x) = Fintype.card (Fin (nMach x)) := by
  rw [Fintype.card_fin]
  simp only [nMach, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

/-- Numbering the jobs is a bijection: there are as many names as numbers, and distinct
names get distinct numbers. -/
noncomputable def jobEquiv : JobS x ≃ Fin (nJobs x) :=
  Equiv.ofBijective (jIdx x)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨jIdx_injective x, card_JobS x⟩)

/-- Numbering the machines is a bijection. -/
noncomputable def machEquiv : MachS x ≃ Fin (nMach x) :=
  Equiv.ofBijective (mIdx x)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨mIdx_injective x, card_MachS x⟩)

end Lax888481Proofs.Construction2
