import Lax759944.RamPolytime

/-!
---
title: Polynomial-Time Many-One Reductions on the Word RAM
type: definition
---
A *polynomial-time many-one reduction* from one set of words to another is a map on
words, computable by a word RAM program in time polynomial in the bit-size of its input,
that preserves and reflects membership. A reduction whose image additionally lies in a
given class witnesses hardness on that class.

# Formalization Notes

Computability is `Lax759944.RamPolytime`, which measures time in the bit-size of the
input rather than the number of entries, and quantifies the program before the word
length as everything on this machine does. Taking it rather than restating it is the
point: the same submission proves it equivalent to polynomial time on a Turing machine,
so a reduction certified here is a reduction in the classical sense, and no statement of
this submission has to choose between the two models.

Both directions of membership are required, as for any many-one reduction: a map
preserving yes-instances only would not transport hardness.

The class a reduction lands in is a predicate on words, and appears as a third
conjunct rather than by restricting the target set. Keeping it separate lets one
reduction witness both a plain hardness claim and a claim on a slice; the second theorem of
this submission needs both.
-/

namespace Lax888481.PolynomialReduction

/-- `P` reduces to `Q` in polynomial time on the word RAM. -/
def PolyReduces (P Q : Set (List ℕ)) : Prop :=
  ∃ f : List ℕ → List ℕ,
    Lax759944.RamPolytime.RamPolytime f ∧ ∀ x, (x ∈ P ↔ f x ∈ Q)

/-- `P` reduces to `Q` in polynomial time by a reduction whose image lies in `C`. -/
def PolyReducesOn (P Q : Set (List ℕ)) (C : List ℕ → Prop) : Prop :=
  ∃ f : List ℕ → List ℕ,
    Lax759944.RamPolytime.RamPolytime f ∧ (∀ x, C (f x)) ∧ ∀ x, (x ∈ P ↔ f x ∈ Q)

end Lax888481.PolynomialReduction
