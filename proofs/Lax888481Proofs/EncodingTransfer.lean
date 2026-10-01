import Lax888481.InstanceEncoding

/-!
A word determines the instance it encodes, as far as anything asked of an instance can
tell. Two instances with the same encoding have the same job and machine counts, the
same processing times, deadlines and weights, and the same eligible sets; so a schedule
for one is a schedule for the other, and the properties the theorems are about transfer.

So a statement can be made about the *word* — "some instance this word
encodes can schedule every job", "some instance this word encodes achieves this
weight" — without the choice of instance mattering.
-/

namespace Lax888481Proofs.EncodingTransfer

open Lax888481.Scheduling Lax888481.InstanceEncoding

variable {y : List ℕ} {I J : Instance}

theorem jobs_eq (hI : EncodesInstance y I) (hJ : EncodesInstance y J) : I.jobs = J.jobs := by
  rw [← hI.jobCount_eq, hJ.jobCount_eq]

theorem machines_eq (hI : EncodesInstance y I) (hJ : EncodesInstance y J) :
    I.machines = J.machines := by
  rw [← hI.machineCount_eq, hJ.machineCount_eq]

private lemma map_eq_some_iff {α β : Type} {f : α → β} {o : Option α} {b : β} :
    o.map f = some b ↔ ∃ a, o = some a ∧ f a = b := by cases o <;> simp

private lemma map_eq_none_iff {α β : Type} {f : α → β} {o : Option α} :
    o.map f = none ↔ o = none := by cases o <;> simp

theorem p_cast (hI : EncodesInstance y I) (hJ : EncodesInstance y J) (j : Fin I.jobs) :
    J.p (Fin.cast (jobs_eq hI hJ) j) = I.p j := by
  rw [← hJ.proc_eq (Fin.cast (jobs_eq hI hJ) j), ← hI.proc_eq j]; rfl

theorem d_cast (hI : EncodesInstance y I) (hJ : EncodesInstance y J) (j : Fin I.jobs) :
    J.d (Fin.cast (jobs_eq hI hJ) j) = I.d j := by
  rw [← hJ.due_eq (Fin.cast (jobs_eq hI hJ) j), ← hI.due_eq j]; rfl

theorem w_cast (hI : EncodesInstance y I) (hJ : EncodesInstance y J) (j : Fin I.jobs) :
    J.w (Fin.cast (jobs_eq hI hJ) j) = I.w j := by
  rw [← hJ.wt_eq (Fin.cast (jobs_eq hI hJ) j), ← hI.wt_eq j]; rfl

theorem start_cast (hI : EncodesInstance y I) (hJ : EncodesInstance y J) (j : Fin I.jobs) :
    J.start (Fin.cast (jobs_eq hI hJ) j) = I.start j := by
  simp only [Instance.start, p_cast hI hJ, d_cast hI hJ]

theorem elig_cast (hI : EncodesInstance y I) (hJ : EncodesInstance y J)
    (j : Fin I.jobs) (i : Fin I.machines) :
    i ∈ I.eligible j ↔
      Fin.cast (machines_eq hI hJ) i ∈ J.eligible (Fin.cast (jobs_eq hI hJ) j) := by
  rw [hI.eligible_iff j i,
    hJ.eligible_iff (Fin.cast (jobs_eq hI hJ) j) (Fin.cast (machines_eq hI hJ) i)]
  rfl

/-- The schedule `σ` read in `J`'s numbering. -/
def cast (hI : EncodesInstance y I) (hJ : EncodesInstance y J) (σ : I.Schedule) :
    J.Schedule :=
  fun j => (σ (Fin.cast (jobs_eq hI hJ).symm j)).map (Fin.cast (machines_eq hI hJ))

/-- **Transporting a feasible schedule along the two encodings.** -/
theorem feasible_cast (hI : EncodesInstance y I) (hJ : EncodesInstance y J)
    {σ : I.Schedule} (hfeas : I.Feasible σ) : J.Feasible (cast hI hJ σ) := by
  have hj := jobs_eq hI hJ
  have hm := machines_eq hI hJ
  constructor
  · intro j i hji
    obtain ⟨i₀, hs, rfl⟩ := map_eq_some_iff.mp hji
    have hmem := (elig_cast hI hJ (Fin.cast hj.symm j) i₀).mp (hfeas.1 _ _ hs)
    have hcj : Fin.cast hj (Fin.cast hj.symm j) = j := Fin.ext rfl
    rwa [hcj] at hmem
  · intro j j' i hne hov hji hji'
    obtain ⟨i₀, hs, hm₀⟩ := map_eq_some_iff.mp hji
    obtain ⟨i₁, hs', hm₁⟩ := map_eq_some_iff.mp hji'
    have hii : i₀ = i₁ :=
      Fin.ext (by simpa using congrArg Fin.val (hm₀.trans hm₁.symm))
    subst hii
    refine hfeas.2 (Fin.cast hj.symm j) (Fin.cast hj.symm j') i₀ ?_ ?_ hs hs'
    · exact fun hc => hne (Fin.ext (by simpa using congrArg Fin.val hc))
    · obtain ⟨h1, h2⟩ := hov
      have e1 := start_cast hI hJ (Fin.cast hj.symm j)
      have e2 := start_cast hI hJ (Fin.cast hj.symm j')
      have e3 := d_cast hI hJ (Fin.cast hj.symm j)
      have e4 := d_cast hI hJ (Fin.cast hj.symm j')
      have hcj : Fin.cast hj (Fin.cast hj.symm j) = j := Fin.ext rfl
      have hcj' : Fin.cast hj (Fin.cast hj.symm j') = j' := Fin.ext rfl
      rw [hcj] at e1 e3
      rw [hcj'] at e2 e4
      exact ⟨by omega, by omega⟩

/-- Transporting a complete feasible schedule along the two encodings. -/
theorem allSchedulable_imp (hI : EncodesInstance y I) (hJ : EncodesInstance y J)
    (h : I.AllSchedulable) : J.AllSchedulable := by
  obtain ⟨σ, hfeas, hall⟩ := h
  refine ⟨cast hI hJ σ, feasible_cast hI hJ hfeas, ?_⟩
  intro j hc
  exact hall (Fin.cast (jobs_eq hI hJ).symm j) (map_eq_none_iff.mp hc)

/-- The transported schedule has the same weight, because the jobs correspond and the
weights agree. -/
theorem weight_cast (hI : EncodesInstance y I) (hJ : EncodesInstance y J)
    (σ : I.Schedule) : J.weight (cast hI hJ σ) = I.weight σ := by
  have hj := jobs_eq hI hJ
  rw [Instance.weight, Instance.weight]
  refine (Fintype.sum_equiv (finCongr hj) _ _ ?_).symm
  intro j
  show (σ j).elim 0 (fun _ => I.w j)
    = ((σ (Fin.cast hj.symm (Fin.cast hj j))).map (Fin.cast (machines_eq hI hJ))).elim 0
        (fun _ => J.w (Fin.cast hj j))
  have hcj : Fin.cast hj.symm (Fin.cast hj j) = j := Fin.ext rfl
  rw [hcj, w_cast hI hJ j]
  rcases σ j with _ | i <;> rfl

/-- **Transporting an achievable weight along the two encodings.** -/
theorem hasWeight_imp (hI : EncodesInstance y I) (hJ : EncodesInstance y J) {W : ℕ}
    (h : I.HasWeight W) : J.HasWeight W := by
  obtain ⟨σ, hfeas, hw⟩ := h
  exact ⟨cast hI hJ σ, feasible_cast hI hJ hfeas, by rw [weight_cast hI hJ σ]; exact hw⟩

/-- **Transporting an achievable weight along two decision encodings.** A decision word
is an instance word followed by its threshold, so the threshold is determined too. -/
theorem hasWeight_dec {z : List ℕ} {W W' : ℕ}
    (hI : EncodesDecisionInstance z I W) (hJ : EncodesDecisionInstance z J W')
    (h : I.HasWeight W) : J.HasWeight W' := by
  obtain ⟨u, hz, hu⟩ := hI
  obtain ⟨u', hz', hu'⟩ := hJ
  obtain ⟨huu, hww⟩ := List.append_inj' (hz.symm.trans hz') rfl
  subst huu
  have hWW : W = W' := by simpa using hww
  subst hWW
  exact hasWeight_imp hu hu' h

end Lax888481Proofs.EncodingTransfer
