import Lax470956Proofs.EncodingTransfer

/-!
The instance a malformed word is sent to.

Both reductions are total maps on words, so both have to say what they do with a word
that is not an instance of the source problem. Both send it to the same place: one job
of processing time, deadline and weight one, and no machine to run it on. Feasibility
forces the only schedule to reject that job, so the instance schedules nothing and
achieves weight zero — it is a no-instance of both scheduling problems at once, which is
what the source problems say about a word they do not recognize.
-/

namespace Lax470956Proofs.NoInstance

open Lax470956.Scheduling Lax470956.InstanceEncoding

/-- One job, no machine. -/
def noInst : Instance where
  jobs := 1
  machines := 0
  p _ := 1
  d _ := 1
  w _ := 1
  eligible _ := ∅
  p_pos _ := Nat.one_pos
  p_le_d _ := le_refl 1

/-- The word that presents it. -/
def word : List ℕ := [1, 0, 1, 1, 1, 0, 0]

theorem encodes_word : EncodesInstance word noInst where
  jobCount_eq := rfl
  machineCount_eq := rfl
  length_eq := rfl
  proc_eq := fun j => by
    have hj : (j : ℕ) = 0 := by have := j.isLt; simp only [noInst] at this; omega
    simp [proc, word, noInst, hj]
  due_eq := fun j => by
    have hj : (j : ℕ) = 0 := by have := j.isLt; simp only [noInst] at this; omega
    simp [due, word, jobCount, noInst, hj]
  wt_eq := fun j => by
    have hj : (j : ℕ) = 0 := by have := j.isLt; simp only [noInst] at this; omega
    simp [wt, word, jobCount, noInst, hj]
  offset_zero := rfl
  offset_mono := fun j hj => by
    have : j = 0 := by simp only [noInst] at hj; omega
    subst this
    simp [offset, word, jobCount]
  target_lt := fun t ht => by simp [offset, word, jobCount, noInst] at ht
  eligible_iff := fun _ i => i.elim0

/-- The word together with the threshold one. -/
theorem encodes_decision : EncodesDecisionInstance (word ++ [1]) noInst 1 :=
  ⟨word, rfl, encodes_word⟩

theorem not_allSchedulable : ¬ noInst.AllSchedulable := by
  rintro ⟨σ, -, hall⟩
  rcases h : σ ⟨0, Nat.one_pos⟩ with _ | i
  · exact hall _ h
  · exact i.elim0

/-- Its only job has no machine, so every feasible schedule rejects it and the weight is
zero. -/
theorem not_hasWeight : ¬ noInst.HasWeight 1 := by
  rintro ⟨σ, -, hw⟩
  have hz : noInst.weight σ = 0 := by
    unfold Instance.weight
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases h : σ j with _ | i
    · rfl
    · exact i.elim0
  omega

end Lax470956Proofs.NoInstance
