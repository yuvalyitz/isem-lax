import Lax470956Proofs.Construction2
import Lax470956Proofs.Emit
import Lax470956Proofs.EncodingTransfer
import Lax470956Proofs.NoInstance

/-!
Construction 2 as a total map on words.

A reduction is a function on *all* words, so the map has to say what it does with a word
that is not a formula. It sends it to a fixed instance with one job and no machine, which
cannot schedule that job; so a malformed word is a no-instance, as it is for the source
problem.
-/

namespace Lax470956Proofs.Reduce

open Lax470956.Scheduling Lax470956.InstanceEncoding Lax470956.Exact34Encoding
open Lax470956.Construction2 Lax470956Proofs.Emit Lax470956Proofs.EncodingTransfer
open Lax470956Proofs

/-- The instance a malformed word is sent to: one job, no machine. -/
abbrev noInst : Instance := NoInstance.noInst

theorem encodes_noWord : EncodesInstance noWord noInst := NoInstance.encodes_word

theorem not_allSchedulable_noInst : ¬ noInst.AllSchedulable := NoInstance.not_allSchedulable

/--
---
conclusion: Lax470956.Construction2.reduce_correct
---
On a well-formed formula the map is Construction 2 and the claim is the correctness of
the construction, transported along the encoding; on any other word both sides are false,
the left because satisfiability asks for well-formedness and the right because the
instance the word is sent to has a job and no machine to run it on.
-/
theorem reduce_correct (x : List ℕ) :
    x ∈ Satisfiable ↔ ∃ I, EncodesInstance (reduce x) I ∧ I.AllSchedulable := by
  by_cases hwf : WellFormed x
  · have hr : reduce x = emit x := by simp [reduce, hwf]
    rw [hr]
    constructor
    · rintro ⟨-, τ, hτ⟩
      exact ⟨inst x, Lax470956Proofs.Emit.emit_encodes x hwf,
        (Lax470956Proofs.Construction2.correct x hwf).mp ⟨τ, hτ⟩⟩
    · rintro ⟨I, hI, hall⟩
      exact ⟨hwf, (Lax470956Proofs.Construction2.correct x hwf).mpr
        (allSchedulable_imp hI (Lax470956Proofs.Emit.emit_encodes x hwf) hall)⟩
  · have hr : reduce x = noWord := by simp [reduce, hwf]
    rw [hr]
    constructor
    · rintro ⟨h, -⟩
      exact absurd h hwf
    · rintro ⟨I, hI, hall⟩
      exact absurd (allSchedulable_imp hI encodes_noWord hall) not_allSchedulable_noInst

/--
---
conclusion: Lax470956.Construction2.reduce_slice
---
On a well-formed formula this is the pair of size bounds already proved of the
construction; on any other word the fixed instance has one job of processing time one
and weight one.
-/
theorem reduce_slice (x : List ℕ) :
    ∃ I, EncodesInstance (reduce x) I ∧ I.pmax ≤ 25 ∧ ∀ j, I.w j = 1 := by
  by_cases hwf : WellFormed x
  · have hr : reduce x = emit x := by simp [reduce, hwf]
    rw [hr]
    exact ⟨inst x, Lax470956Proofs.Emit.emit_encodes x hwf,
      Lax470956Proofs.Construction2.pmax_le x,
      fun j => Lax470956Proofs.Construction2.weights_one x j⟩
  · have hr : reduce x = noWord := by simp [reduce, hwf]
    rw [hr]
    refine ⟨noInst, encodes_noWord, ?_, fun _ => rfl⟩
    simp [Instance.pmax, noInst, NoInstance.noInst]

end Lax470956Proofs.Reduce
