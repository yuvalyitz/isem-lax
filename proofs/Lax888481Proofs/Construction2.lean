import Lax888481Proofs.Construction2Lemma4

/-!
The two size properties of Construction 2's output: unit weights and processing times
bounded by an absolute constant. Both are immediate from the definition, and together
they are what places the reduction's image in the slice the second theorem is about.
-/

namespace Lax888481Proofs.Construction2

open Lax888481.Scheduling Lax888481.Exact34Encoding Lax888481.Construction2

/--
---
conclusion: Lax888481.Construction2.weights_one
---
Every job of the construction is given weight one by definition.
-/
theorem weights_one (x : List ℕ) (j : Fin (inst x).jobs) : (inst x).w j = 1 := rfl

/--
---
conclusion: Lax888481.Construction2.pmax_le
---
The largest processing time is a supremum over the jobs, and every one of the four
kinds of job has a processing time of at most `25`: the variable job is exactly `25`,
a literal job is `1`, and the two wrappers are `dl - 1` and `25 - dl` with `dl` clamped
to `[2, 24]`.
-/
theorem pmax_le (x : List ℕ) : (inst x).pmax ≤ 25 :=
  Finset.sup_le fun j _ => procOf_le_25 x j

/--
---
conclusion: Lax888481.Construction2.correct
---
The two halves of the paper's Section 4. From a satisfying assignment, `lemma3` builds
the schedule: each variable job goes on the machine opposing its value, freeing the
agreeing machine for the selected literal of every clause that variable satisfies, and
the remaining jobs of a clause are distributed over its own three machines by the
transposition exchanging the selected literal with the first.

Conversely `lemma4` reads the assignment off a schedule. `observation4` first shows that
the two wrapper jobs of each literal share a machine — all three wrappers of one side
pairwise overlap, so they are spread bijectively over the clause's machines, and the
evenness of the deadlines forces that bijection to be the identity. Machine `0` of the
clause is then blocked for two literals, and the third literal job has nowhere to go but
its variable machine, which pins the variable job to the opposite one.
-/
theorem correct (x : List ℕ) (hwf : WellFormed x) :
    (∃ τ, Satisfies x τ) ↔ (inst x).AllSchedulable := by
  refine ⟨lemma3 hwf, fun h => ?_⟩
  obtain ⟨σ, hfeas, hall⟩ := named_of_allSchedulable h
  exact lemma4 hfeas hall hwf

end Lax888481Proofs.Construction2
