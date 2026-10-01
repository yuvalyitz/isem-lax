import Lax429075.Reductions
import Lax429075.Satisfiability
import Lax470956.NPHardness

/-!
---
title: (3,4)-satisfiability
type: definition
---
*(3,4)-SAT* is satisfiability restricted to formulas in which every clause contains
exactly three literals and every variable occurs at most four times. Tovey proved
that it is NP-hard; it is the starting point of the second theorem of this submission,
because the bounded number of occurrences is what keeps the processing times of the
scheduling instance the reduction builds bounded by an absolute constant.

# Formalization notes

The restriction is a predicate on the CNF formulas of the archive's Cook–Levin submission,
so the encoding and the notion of satisfiability are shared with unrestricted SAT.
Occurrences are counted with multiplicity.

Tovey's theorem is stated here, and proved in the submission `lax-345332`, from which the proofs
of this submission take it: the language of that submission is this one.
-/

namespace Lax470956.SatVariant

open Lax429075.CNF Lax434930.PolynomialTime

/-- The number of occurrences of the variable `i` in the formula `F`. -/
def occurrences (F : Formula) (i : ℕ) : ℕ :=
  (F.flatMap fun C => C.filter fun l => l.index == i).length

/-- The variables occurring in `F`. -/
def occurringVars (F : Formula) : List ℕ := (F.flatMap id).map Literal.index

/-- `F` is a *(3,4)* formula: every clause has exactly three literals, and every variable
occurs at most four times. -/
def Exact34 (F : Formula) : Prop :=
  (∀ C ∈ F, C.length = 3) ∧ ∀ i ∈ occurringVars F, occurrences F i ≤ 4

/-- **(3,4)-SAT** as a language: the encodings of satisfiable (3,4)
formulas. -/
def SAT34 : Language :=
  {w | ∃ F : Formula, Lax429075.Encoding.encodeCNF F = w ∧ Exact34 F ∧ Satisfiable F}

/-- **Tovey's theorem.** (3,4)-SAT is NP-hard.

Tovey, *A simplified NP-complete satisfiability problem*, Discrete Applied Mathematics 8
(1984) 85–89. -/
axiom sat34_npHard :
    ∀ A : Language, A ∈ Lax434930.NondeterministicPolynomialTime.NP →
      Lax429075.Reductions.ManyOne A SAT34

end Lax470956.SatVariant
