import Lax470956Proofs.TypedIsem
import Lax470956.Scheduling

/-!
Renumbering a typed instance into a numbered one, with inert padding.

The paper names jobs and machines structurally; the archive numbers them, and numbering
a family that has no closed-form size means allocating a slot for every candidate and
leaving the ones that are not jobs empty. This file says once that neither step changes
what the instance can do: if the real jobs embed injectively, preserving processing
times, deadlines, weights and eligibility, and every slot outside the embedding has no
eligible machine and no weight, then the two instances admit feasible schedules of
exactly the same weights.

The inert slots are harmless in a strong sense: having no eligible machine, feasibility
alone forces a schedule to reject them, so they cannot be used to block a real job.
-/

namespace Lax470956Proofs.Renumber

open Lax470956.Scheduling Lax470956Proofs.TypedIsem

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A numbering of `I`'s jobs and machines inside `J`, whose unused slots are inert. -/
structure Renumbering (I : ISEM) (J : Instance) where
  /-- Where each job goes. -/
  job : I.Job → Fin J.jobs
  /-- Distinct jobs go to distinct slots. -/
  job_inj : Function.Injective job
  /-- The machines correspond exactly. -/
  mach : I.Machine ≃ Fin J.machines
  /-- Processing times agree. -/
  p_eq : ∀ j, J.p (job j) = I.p j
  /-- Deadlines agree. -/
  d_eq : ∀ j, J.d (job j) = I.d j
  /-- Weights agree. -/
  w_eq : ∀ j, J.w (job j) = I.w j
  /-- Eligibility agrees. -/
  elig_eq : ∀ j, J.eligible (job j) = (I.elig j).image mach
  /-- A slot that is not a job has no eligible machine. -/
  inert_elig : ∀ s, (∀ j, job j ≠ s) → J.eligible s = ∅

namespace Renumbering

variable {I : ISEM} {J : Instance} (R : Renumbering I J)

/-- The intervals agree, so the overlap relations do. -/
lemma start_eq (j : I.Job) : J.start (R.job j) = I.start j := by
  simp only [Instance.start, ISEM.start, R.p_eq, R.d_eq]

lemma overlap_iff (j j' : I.Job) : J.Overlap (R.job j) (R.job j') ↔ I.Conflict j j' := by
  simp only [Instance.Overlap, ISEM.Conflict, R.start_eq, R.d_eq]

open Classical in
/-- The job a slot came from, if any. -/
noncomputable def pre (s : Fin J.jobs) : Option I.Job :=
  if hs : ∃ j, R.job j = s then some (Classical.choose hs) else none

open Classical in
lemma pre_job (j : I.Job) : R.pre (R.job j) = some j := by
  have hs : ∃ j', R.job j' = R.job j := ⟨j, rfl⟩
  rw [pre, dif_pos hs]
  exact congrArg some (R.job_inj (Classical.choose_spec hs))

open Classical in
lemma pre_eq_none {s : Fin J.jobs} (hs : ∀ j, R.job j ≠ s) : R.pre s = none := by
  rw [pre, dif_neg]
  rintro ⟨j, hj⟩
  exact hs j hj

open Classical in
lemma pre_eq_some {s : Fin J.jobs} {j : I.Job} (h : R.pre s = some j) : R.job j = s := by
  by_cases hs : ∃ j', R.job j' = s
  · rw [pre, dif_pos hs] at h
    have := Classical.choose_spec hs
    rwa [Option.some_inj.mp h] at this
  · rw [pre, dif_neg hs] at h
    exact absurd h (by simp)

/-- A slot that is not a job is rejected by every feasible schedule. -/
lemma not_scheduled {σ' : J.Schedule} (hfeas : Instance.Feasible σ')
    {s : Fin J.jobs} (hs : ∀ j, R.job j ≠ s) : σ' s = none := by
  rcases hσ : σ' s with _ | i
  · rfl
  · have hmem := hfeas.1 s i hσ
    rw [R.inert_elig s hs] at hmem
    exact absurd hmem (by simp)

/-- The slots that are jobs. -/
noncomputable def img : Finset (Fin J.jobs) := Finset.univ.image R.job

lemma mem_img_iff {s : Fin J.jobs} : s ∈ R.img ↔ ∃ j, R.job j = s := by
  simp [img]

/-- Summing over the slots is summing over the jobs, because the others contribute
nothing. -/
lemma sum_slots (F : Fin J.jobs → ℕ) (hF : ∀ s, (∀ j, R.job j ≠ s) → F s = 0) :
    ∑ s : Fin J.jobs, F s = ∑ j : I.Job, F (R.job j) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ R.img)]
  · rw [img, Finset.sum_image (fun a _ b _ h => R.job_inj h)]
  · intro s _ hs
    refine hF s ?_
    intro j hj
    exact hs (R.mem_img_iff.mpr ⟨j, hj⟩)

/-- **Renumbering preserves the achievable weights.** -/
theorem hasWeight_iff (R : Renumbering I J) (W : ℕ) : I.HasWeight W ↔ J.HasWeight W := by
  classical
  constructor
  · rintro ⟨σ, hfeas, hw⟩
    refine ⟨fun s => (R.pre s).bind fun j => (σ j).map R.mach, ?_, ?_⟩
    · constructor
      · intro s i hsi
        dsimp only at hsi
        rcases hp : R.pre s with _ | j
        · rw [hp] at hsi; exact absurd hsi (by simp)
        · rw [hp] at hsi
          simp only [Option.bind_some] at hsi
          rcases hσ : σ j with _ | m
          · rw [hσ] at hsi; exact absurd hsi (by simp)
          · rw [hσ, Option.map_some] at hsi
            have hi : i = R.mach m := (Option.some_inj.mp hsi).symm
            rw [← R.pre_eq_some hp, R.elig_eq j, hi]
            exact Finset.mem_image_of_mem _ (hfeas.1 j m hσ)
      · intro s s' i hne hov hsi
        dsimp only at hsi ⊢
        rcases hp : R.pre s with _ | j
        · rw [hp] at hsi; exact absurd hsi (by simp)
        · rcases hp' : R.pre s' with _ | j'
          · simp [hp']
          · rw [hp] at hsi
            simp only [Option.bind_some] at hsi
            rcases hσ : σ j with _ | m
            · rw [hσ] at hsi; exact absurd hsi (by simp)
            · rw [hσ, Option.map_some] at hsi
              have hi : i = R.mach m := (Option.some_inj.mp hsi).symm
              simp only [Option.bind_some]
              rcases hσ' : σ j' with _ | m'
              · simp
              · rw [Option.map_some]
                intro hcon
                have hm : m' = m := R.mach.injective
                  (by rw [← hi]; exact (Option.some_inj.mp hcon))
                have hjne : j ≠ j' := by
                  rintro rfl
                  exact hne ((R.pre_eq_some hp).symm.trans (R.pre_eq_some hp'))
                have hconf : I.Conflict j j' := by
                  rw [← R.overlap_iff]
                  rwa [R.pre_eq_some hp, R.pre_eq_some hp']
                exact hfeas.2 j j' m hjne hconf hσ (by rw [hσ', hm])
    · refine le_trans hw (le_of_eq ?_)
      rw [ISEM.weight, Instance.weight]
      rw [R.sum_slots (fun s => ((R.pre s).bind fun j => (σ j).map R.mach).elim 0
        fun _ => J.w s) ?_]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [R.pre_job j, R.w_eq j]
        rcases hσ : σ j with _ | m <;> simp [hσ]
      · intro s hs
        rw [R.pre_eq_none hs]
        rfl
  · rintro ⟨σ', hfeas, hw⟩
    refine ⟨fun j => (σ' (R.job j)).map R.mach.symm, ?_, ?_⟩
    · constructor
      · intro j m hjm
        dsimp only at hjm
        rcases hσ : σ' (R.job j) with _ | i
        · rw [hσ] at hjm; exact absurd hjm (by simp)
        · rw [hσ, Option.map_some] at hjm
          have hm : m = R.mach.symm i := (Option.some_inj.mp hjm).symm
          have hmem := hfeas.1 (R.job j) i hσ
          rw [R.elig_eq j] at hmem
          obtain ⟨m', hm', hmm'⟩ := Finset.mem_image.mp hmem
          rw [hm, ← hmm']
          simpa using hm'
      · intro j j' m hne hconf hjm
        dsimp only at hjm ⊢
        rcases hσ : σ' (R.job j) with _ | i
        · rw [hσ] at hjm; exact absurd hjm (by simp)
        · rw [hσ, Option.map_some] at hjm
          have hm : m = R.mach.symm i := (Option.some_inj.mp hjm).symm
          rcases hσ' : σ' (R.job j') with _ | i'
          · simp [hσ']
          · rw [Option.map_some]
            intro hcon
            have hii : i' = i := by
              have := (Option.some_inj.mp hcon).trans hm
              simpa using congrArg R.mach this
            subst hii
            have hjne : R.job j ≠ R.job j' := fun h => hne (R.job_inj h)
            have hov : J.Overlap (R.job j) (R.job j') := (R.overlap_iff j j').mpr hconf
            exact hfeas.2 (R.job j) (R.job j') i' hjne hov hσ hσ'
    · refine le_trans hw (le_of_eq ?_)
      rw [ISEM.weight, Instance.weight]
      rw [R.sum_slots (fun s => (σ' s).elim 0 fun _ => J.w s) ?_]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [R.w_eq j]
        rcases hσ : σ' (R.job j) with _ | i <;> simp [hσ]
      · intro s hs
        rw [R.not_scheduled hfeas hs]
        rfl

end Renumbering

end Lax470956Proofs.Renumber
