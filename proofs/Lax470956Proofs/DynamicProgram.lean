import Lax470956.Preprocessing
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Common

/-!
Lemma 6 and the state-space bound: the dynamic program of Section 5.2 computes the
optimum, and at any instant it has at most `(a_t + 1) ^ m` states to consider.

The pivot is that a feasible schedule and a *run* — the time-indexed record of which job
occupies each machine — are the same thing. `runOf` turns a schedule into its run, and
`extend` and `pick` turn a run back into a schedule, one time step at a time. The
recursion is then an induction over that correspondence: `optAt_zero` is the base case
and `optAt_succ` the step, and `dp_eq_optAt_aux` puts them together.
-/

namespace Lax470956Proofs.DynamicProgram

open Lax470956.Scheduling Lax470956.Scheduling.Instance Lax470956.DynamicProgram Lax470956.Preprocessing

variable (I : Instance)

/-- Overlap is symmetric. -/
lemma overlap_symm {j j' : Fin I.jobs} (h : I.Overlap j j') : I.Overlap j' j := ⟨h.2, h.1⟩

lemma active_start (j : Fin I.jobs) : Active (I.start j) j := by
  refine ⟨le_rfl, ?_⟩
  have h1 := I.p_pos j
  have h2 := I.p_le_d j
  change I.d j - I.p j < I.d j
  omega

variable {I}

lemma runOf_eq_some {σ : I.Schedule} {t : ℕ} {i : Fin I.machines} {j : Fin I.jobs}
    (hfeas : Feasible σ) (hj : σ j = some i) (hact : Active t j) :
    runOf σ t i = some j := by
  have hex : ∃ j, σ j = some i ∧ Active t j := ⟨j, hj, hact⟩
  rw [runOf, dif_pos hex]
  obtain ⟨hj', hact'⟩ := hex.choose_spec
  congr 1
  by_contra hne
  exact hfeas.2 hex.choose j i hne
    ⟨lt_of_le_of_lt hact'.1 hact.2, lt_of_le_of_lt hact.1 hact'.2⟩ hj' hj

lemma runOf_some {σ : I.Schedule} {t : ℕ} {i : Fin I.machines} {j : Fin I.jobs}
    (h : runOf σ t i = some j) : σ j = some i ∧ Active t j := by
  rw [runOf] at h
  split at h
  · rename_i hex
    obtain ⟨hj', hact'⟩ := hex.choose_spec
    rw [Option.some.injEq] at h
    subst h
    exact ⟨hj', hact'⟩
  · exact absurd h (by simp)

variable (I)

lemma d_le_horizon (j : Fin I.jobs) : I.d j ≤ horizon I := Finset.le_sup (Finset.mem_univ j)

lemma start_le_horizon (j : Fin I.jobs) : I.start j ≤ horizon I :=
  le_trans (Nat.sub_le _ _) (d_le_horizon I j)

lemma weightStarted_horizon (σ : I.Schedule) : weightStarted I σ (horizon I) = weight σ := by
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : σ j = none
  · rw [if_neg (by simp [h]), h]; rfl
  · rw [if_pos ⟨h, start_le_horizon I j⟩]
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp h
    rw [hi]; rfl

variable {I}

lemma validState_runOf {σ : I.Schedule} (hfeas : Feasible σ) (t : ℕ) :
    ValidState I t (runOf σ t) := by
  refine ⟨fun i j h => ⟨hfeas.1 j i (runOf_some h).1, (runOf_some h).2⟩, fun i i' j h h' => ?_⟩
  have h1 := (runOf_some h).1
  have h2 := (runOf_some h').1
  rw [h1] at h2
  exact Option.some.inj h2

lemma step_runOf {σ : I.Schedule} (hfeas : Feasible σ) (t : ℕ) :
    Step I t (runOf σ t) (runOf σ (t + 1)) := by
  refine ⟨validState_runOf hfeas (t + 1), fun i j h hlt => ?_, fun i j h hs => ?_⟩
  · obtain ⟨hj, ha1, ha2⟩ := runOf_some h
    exact runOf_eq_some hfeas hj ⟨by omega, hlt⟩
  · obtain ⟨hj, ha1, ha2⟩ := runOf_some h
    exact runOf_eq_some hfeas hj ⟨hs, by omega⟩

lemma exists_runOf_iff {σ : I.Schedule} (hfeas : Feasible σ) {t : ℕ} {j : Fin I.jobs}
    (hact : Active t j) : (∃ i, runOf σ t i = some j) ↔ σ j ≠ none := by
  constructor
  · rintro ⟨i, hi⟩; rw [(runOf_some hi).1]; simp
  · intro h
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨i, runOf_eq_some hfeas hi hact⟩

lemma weightStarted_succ {σ : I.Schedule} (hfeas : Feasible σ) (t : ℕ) :
    weightStarted I σ (t + 1)
      = weightStarted I σ t + freshWeight I (t + 1) (runOf σ (t + 1)) := by
  rw [weightStarted, weightStarted, freshWeight, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : σ j = none
  · have hnex : ¬ ∃ i, runOf σ (t + 1) i = some j := by
      rintro ⟨i, hi⟩
      rw [(runOf_some hi).1] at h1
      simp at h1
    rw [if_neg (by rintro ⟨h4, -⟩; exact h4 h1), if_neg (by rintro ⟨h4, -⟩; exact h4 h1),
      if_neg (by rintro ⟨h4, -⟩; exact hnex h4)]
  by_cases h2 : I.start j ≤ t
  · rw [if_pos ⟨h1, by omega⟩, if_pos ⟨h1, h2⟩, if_neg (by rintro ⟨-, h3⟩; omega)]
    omega
  by_cases h3 : I.start j = t + 1
  · have hact : Active (t + 1) j := by
      refine ⟨by omega, ?_⟩
      have h5 := (active_start I j).2
      omega
    rw [if_pos ⟨h1, by omega⟩, if_neg (by rintro ⟨-, h4⟩; omega),
      if_pos ⟨(exists_runOf_iff hfeas hact).mpr h1, h3⟩]
    omega
  · rw [if_neg (by rintro ⟨-, h4⟩; omega), if_neg (by rintro ⟨-, h4⟩; omega),
      if_neg (by rintro ⟨-, h4⟩; omega)]

/-! ### Extending a Schedule Across One Time Step -/

open scoped Classical in
/-- Given a feasible schedule realising `s` at time `t`, and a successor state `s'`,
rebuild the schedule so that it realises `s'` at time `t+1`: keep every job that had
already started, and start exactly the jobs that `s'` shows beginning at `t+1`. -/
noncomputable def extend (σ : I.Schedule) (t : ℕ) (s' : State I) : I.Schedule := fun j =>
  if I.start j ≤ t then σ j
  else if h : ∃ i, s' i = some j then some h.choose
  else none

variable {σ : I.Schedule} {t : ℕ} {s' : State I} {j : Fin I.jobs}

lemma extend_of_le (h : I.start j ≤ t) : extend σ t s' j = σ j := by
  rw [extend, if_pos h]

lemma extend_of_mem (hval : ValidState I (t + 1) s') {i : Fin I.machines} {j : Fin I.jobs}
    (hij : s' i = some j) (hgt : ¬ I.start j ≤ t) : extend σ t s' j = some i := by
  have hex : ∃ i, s' i = some j := ⟨i, hij⟩
  rw [extend, if_neg hgt, dif_pos hex]
  exact congrArg some (hval.2 _ _ _ hex.choose_spec hij)

lemma extend_some {j : Fin I.jobs} {i : Fin I.machines} (h : extend σ t s' j = some i) :
    (I.start j ≤ t ∧ σ j = some i) ∨ (¬ I.start j ≤ t ∧ s' i = some j) := by
  rw [extend] at h
  split at h
  · exact Or.inl ⟨by assumption, h⟩
  · rename_i hgt
    split at h
    · rename_i hex
      have := hex.choose_spec
      rw [Option.some.injEq] at h
      subst h
      exact Or.inr ⟨hgt, this⟩
    · exact absurd h (by simp)

lemma extend_eq_none {j : Fin I.jobs} (hgt : ¬ I.start j ≤ t) (hnex : ¬ ∃ i, s' i = some j) :
    extend σ t s' j = none := by
  rw [extend, if_neg hgt, dif_neg hnex]

/-- The extended schedule realises `s'` at time `t+1`. -/
theorem runOf_extend (hfeas : Feasible σ) (hstep : Step I t (runOf σ t) s')
    (hfe : Feasible (extend σ t s')) : runOf (extend σ t s') (t + 1) = s' := by
  obtain ⟨hval, hcont, hback⟩ := hstep
  funext i
  rcases hi : s' i with _ | j
  · rcases hr : runOf (extend σ t s') (t + 1) i with _ | j'
    · rfl
    · exfalso
      obtain ⟨hj', hact'⟩ := runOf_some hr
      rcases extend_some hj' with ⟨hle, hσ⟩ | ⟨hgt, hs'⟩
      · have hactt : Active t j' := ⟨hle, by have := hact'.2; omega⟩
        have := hcont i j' (runOf_eq_some hfeas hσ hactt) hact'.2
        rw [hi] at this
        exact absurd this (by simp)
      · rw [hi] at hs'
        exact absurd hs' (by simp)
  · refine runOf_eq_some hfe ?_ (hval.1 i j hi).2
    by_cases hle : I.start j ≤ t
    · rw [extend_of_le hle]
      exact (runOf_some (hback i j hi hle)).1
    · exact extend_of_mem hval hi hle

/-- The extended schedule is feasible. -/
theorem feasible_extend (hfeas : Feasible σ) (hstep : Step I t (runOf σ t) s') :
    Feasible (extend σ t s') := by
  obtain ⟨hval, hcont, hback⟩ := hstep
  refine ⟨fun j i h => ?_, fun j j' i hne hconf hj hj' => ?_⟩
  · rcases extend_some h with ⟨-, hσ⟩ | ⟨-, hs'⟩
    · exact hfeas.1 j i hσ
    · exact (hval.1 i j hs').1
  · -- two conflicting jobs cannot share a machine
    rcases extend_some hj with ⟨hle, hσ⟩ | ⟨hgt, hs'⟩ <;>
      rcases extend_some hj' with ⟨hle', hσ'⟩ | ⟨hgt', hs''⟩
    · exact hfeas.2 j j' i hne hconf hσ hσ'
    · -- `j` old on `i`, `j'` new on `i`
      obtain ⟨-, hA1, hA2⟩ := hval.1 i j' hs''
      have h5 := hconf.2
      have hdj : t + 1 < I.d j := by omega
      have hactt : Active t j := ⟨hle, by omega⟩
      have h6 := hcont i j (runOf_eq_some hfeas hσ hactt) hdj
      rw [hs''] at h6
      exact hne (Option.some.inj h6).symm
    · -- symmetric
      obtain ⟨-, hA1, hA2⟩ := hval.1 i j hs'
      have h5 := hconf.1
      have hdj : t + 1 < I.d j' := by omega
      have hactt : Active t j' := ⟨hle', by omega⟩
      have h6 := hcont i j' (runOf_eq_some hfeas hσ' hactt) hdj
      rw [hs'] at h6
      exact hne (Option.some.inj h6)
    · rw [hs'] at hs''
      exact hne (Option.some.inj hs'')

/-- Extending adds exactly the weight of the jobs beginning at `t+1`. -/
theorem weightStarted_extend (hval : ValidState I (t + 1) s') :
    weightStarted I (extend σ t s') (t + 1)
      = weightStarted I σ t + freshWeight I (t + 1) s' := by
  rw [weightStarted, weightStarted, freshWeight, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h2 : I.start j ≤ t
  · rw [extend_of_le h2]
    by_cases h1 : σ j = none
    · rw [if_neg (by rintro ⟨h4, -⟩; exact h4 h1), if_neg (by rintro ⟨h4, -⟩; exact h4 h1),
        if_neg (by rintro ⟨-, h4⟩; omega)]
    · rw [if_pos ⟨h1, by omega⟩, if_pos ⟨h1, h2⟩, if_neg (by rintro ⟨-, h4⟩; omega)]
      omega
  · by_cases hex : ∃ i, s' i = some j
    · obtain ⟨i, hi⟩ := hex
      obtain ⟨-, hA1, hA2⟩ := hval.1 i j hi
      have hst : I.start j = t + 1 := by omega
      rw [extend_of_mem hval hi h2]
      rw [if_pos ⟨by simp, by omega⟩, if_neg (by rintro ⟨-, h4⟩; omega),
        if_pos ⟨⟨i, hi⟩, hst⟩]
      omega
    · rw [extend_eq_none h2 hex]
      rw [if_neg (by rintro ⟨h4, -⟩; exact h4 rfl), if_neg (by rintro ⟨-, h4⟩; omega),
        if_neg (by rintro ⟨h4, -⟩; exact hex h4)]

open scoped Classical in
/-- The schedule that realises a single state and nothing else. -/
noncomputable def pick (s : State I) : I.Schedule := fun j =>
  if h : ∃ i, s i = some j then some h.choose else none

lemma pick_some {s : State I} {j : Fin I.jobs} {i : Fin I.machines}
    (h : pick s j = some i) : s i = some j := by
  rw [pick] at h
  split at h
  · rename_i hex
    have hc := hex.choose_spec
    rw [Option.some.injEq] at h
    subst h
    exact hc
  · exact absurd h (by simp)

lemma pick_eq {s : State I} (hval : ValidState I 0 s) {j : Fin I.jobs} {i : Fin I.machines}
    (h : s i = some j) : pick s j = some i := by
  have hex : ∃ i, s i = some j := ⟨i, h⟩
  rw [pick, dif_pos hex]
  exact congrArg some (hval.2 _ _ _ hex.choose_spec h)

lemma pick_ne_none_iff {s : State I} {j : Fin I.jobs} :
    pick s j ≠ none ↔ ∃ i, s i = some j := by
  rw [pick]
  split <;> simp_all

theorem feasible_pick {s : State I} (hval : ValidState I 0 s) : Feasible (pick s) := by
  refine ⟨fun j i h => (hval.1 i j (pick_some h)).1, fun j j' i hne _ hj hj' => ?_⟩
  have h1 := pick_some hj
  have h2 := pick_some hj'
  rw [h1] at h2
  exact hne (Option.some.inj h2)

theorem runOf_pick {s : State I} (hval : ValidState I 0 s) : runOf (pick s) 0 = s := by
  funext i
  rcases hi : s i with _ | j
  · rcases hr : runOf (pick s) 0 i with _ | j'
    · rfl
    · exfalso
      have h5 := pick_some (runOf_some hr).1
      rw [hi] at h5
      exact absurd h5 (by simp)
  · exact runOf_eq_some (feasible_pick hval) (pick_eq hval hi) (hval.1 i j hi).2

theorem weightStarted_pick {s : State I} (hval : ValidState I 0 s) :
    weightStarted I (pick s) 0 = freshWeight I 0 s := by
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hex : ∃ i, s i = some j
  · obtain ⟨i, hi⟩ := hex
    obtain ⟨-, hA1, hA2⟩ := hval.1 i j hi
    rw [if_pos ⟨by rw [pick_eq hval hi]; simp, by omega⟩, if_pos ⟨⟨i, hi⟩, by omega⟩]
  · rw [if_neg (by rintro ⟨h4, -⟩; exact hex (pick_ne_none_iff.mp h4)),
      if_neg (by rintro ⟨h4, -⟩; exact hex h4)]

open scoped Classical in
/-- **Lemma 6, base case.** -/
theorem optAt_zero (s : State I) :
    optAt I 0 s = if ValidState I 0 s then (freshWeight I 0 s : WithBot ℕ) else ⊥ := by
  classical
  rw [optAt]
  by_cases hval : ValidState I 0 s
  · rw [if_pos hval]
    refine le_antisymm (Finset.sup_le fun σ hσ => ?_) ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      obtain ⟨hfeas, hrun⟩ := hσ
      refine le_of_eq (congrArg _ ?_)
      rw [← hrun]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hst : I.start j = 0
      · have hact : Active 0 j := by
          have h5 := (active_start I j).2
          exact ⟨by omega, by omega⟩
        by_cases h1 : σ j = none
        · rw [if_neg (by rintro ⟨h4, -⟩; exact h4 h1),
            if_neg (by rintro ⟨h4, -⟩; exact ((exists_runOf_iff hfeas hact).mp h4) h1)]
        · rw [if_pos ⟨h1, by omega⟩, if_pos ⟨(exists_runOf_iff hfeas hact).mpr h1, hst⟩]
      · rw [if_neg (by rintro ⟨-, h4⟩; omega), if_neg (by rintro ⟨-, h4⟩; omega)]
    · rw [← weightStarted_pick hval]
      refine Finset.le_sup (f := fun σ => (weightStarted I σ 0 : WithBot ℕ)) (b := pick s) ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨feasible_pick hval, runOf_pick hval⟩
  · rw [if_neg hval]
    refine le_antisymm (Finset.sup_le fun σ hσ => ?_) bot_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact absurd (hσ.2 ▸ validState_runOf hσ.1 0) hval

private lemma cast_add_withBot (a b : ℕ) :
    ((a + b : ℕ) : WithBot ℕ) = (a : WithBot ℕ) + (b : WithBot ℕ) := rfl

open scoped Classical in
/-- **Lemma 6, recursive case.** -/
theorem optAt_succ (t : ℕ) (s' : State I) :
    optAt I (t + 1) s'
      = ((Finset.univ.filter (fun s => Step I t s s')).sup (fun s => optAt I t s))
        + (freshWeight I (t + 1) s' : WithBot ℕ) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [optAt]
    refine Finset.sup_le fun σ hσ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨hfeas, hrun⟩ := hσ
    have hstep : Step I t (runOf σ t) s' := hrun ▸ step_runOf hfeas t
    have hw : weightStarted I σ (t + 1)
        = weightStarted I σ t + freshWeight I (t + 1) s' := by
      rw [weightStarted_succ hfeas t, hrun]
    rw [hw, cast_add_withBot]
    have key : (weightStarted I σ t : WithBot ℕ)
        ≤ (Finset.univ.filter (fun s => Step I t s s')).sup (fun s => optAt I t s) :=
      calc (weightStarted I σ t : WithBot ℕ)
          ≤ optAt I t (runOf σ t) := by
            rw [optAt]
            exact Finset.le_sup (f := fun σ => (weightStarted I σ t : WithBot ℕ)) (b := σ)
              (by simpa using hfeas)
        _ ≤ _ := Finset.le_sup (f := fun s => optAt I t s) (b := runOf σ t)
              (by simpa using hstep)
    gcongr
  · rcases Finset.eq_empty_or_nonempty
      (Finset.univ.filter (fun s => Step I t s s')) with hemp | hne
    · rw [hemp]
      simp
    · obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup _ hne (fun s => optAt I t s)
      rw [hsup]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rcases Finset.eq_empty_or_nonempty
        (Finset.univ.filter (fun σ : I.Schedule => Feasible σ ∧ runOf σ t = s)) with hemp | hne2
      · rw [optAt, hemp]
        simp
      · obtain ⟨σ, hσ, hσsup⟩ := Finset.exists_mem_eq_sup _ hne2
          (fun σ => (weightStarted I σ t : WithBot ℕ))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        obtain ⟨hfeas, hrun⟩ := hσ
        have hstep : Step I t (runOf σ t) s' := hrun ▸ hs
        have hfe := feasible_extend hfeas hstep
        have hre := runOf_extend hfeas hstep hfe
        have hkey : ((weightStarted I (extend σ t s') (t + 1) : ℕ) : WithBot ℕ)
            ≤ optAt I (t + 1) s' := by
          rw [optAt]
          refine Finset.le_sup
            (f := fun σ => (weightStarted I σ (t + 1) : WithBot ℕ)) (b := extend σ t s') ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hfe, hre⟩
        rw [weightStarted_extend hstep.1, cast_add_withBot] at hkey
        rw [optAt, hσsup]
        exact hkey

/-! ## 5. The algorithm and its correctness -/

variable (I)

/-- The dynamic program computes `optAt`. -/
theorem dp_eq_optAt_aux (t : ℕ) (s : State I) : dp I t s = optAt I t s := by
  induction t generalizing s with
  | zero => rw [dp, optAt_zero]
  | succ t ih =>
      rw [dp, optAt_succ]
      congr 1
      exact Finset.sup_congr rfl fun s _ => ih s

/-- At the horizon every job has finished, so all machines are idle. -/
theorem runOf_horizon {σ : I.Schedule} : runOf σ (horizon I) = fun _ => none := by
  funext i
  rcases hr : runOf σ (horizon I) i with _ | j
  · rfl
  · exact absurd (runOf_some hr).2.2 (by have := d_le_horizon I j; omega)

/-- **Theorem 3 (algorithmic content).** The dynamic program returns the optimum. -/
theorem dp_horizon : dp I (horizon I) (fun _ => none) = (optimum I : WithBot ℕ) := by
  classical
  rw [dp_eq_optAt_aux, optAt]
  refine le_antisymm (Finset.sup_le fun σ hσ => ?_) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [weightStarted_horizon I σ]
    have h1 : weight σ ≤ optimum I := by
      rw [optimum]; exact Finset.le_sup (f := weight) (by simpa using hσ.1)
    exact WithBot.coe_le_coe.mpr h1
  · have hne : (Finset.univ.filter (fun σ : I.Schedule => Feasible σ)).Nonempty := by
      refine ⟨fun _ => none, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun j i hji => absurd hji (by simp), fun j j' i _ _ hji => absurd hji (by simp)⟩
    obtain ⟨σ, hσ, hmax⟩ := Finset.exists_mem_eq_sup _ hne weight
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [optimum, hmax, ← weightStarted_horizon I σ]
    refine Finset.le_sup
      (f := fun σ => (weightStarted I σ (horizon I) : WithBot ℕ)) (b := σ) ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hσ, runOf_horizon I⟩

theorem solve_eq_optimum_aux : solve I = (optimum I : WithBot ℕ) := dp_horizon I

theorem card_validState_le_aux (t : ℕ) :
    (Finset.univ.filter (fun s : State I => ValidState I t s)).card
      ≤ (aliveCount I t + 1) ^ I.machines := by
  classical
  have hsub : (Finset.univ.filter (fun s : State I => ValidState I t s))
      ⊆ Finset.image
          (fun f : Fin I.machines → Option {j : Fin I.jobs // Active t j} =>
            (fun i => (f i).map Subtype.val : State I))
          Finset.univ := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    refine Finset.mem_image.mpr
      ⟨fun i => Option.pmap (fun j hj => (⟨j, hj⟩ : {j : Fin I.jobs // Active t j})) (s i)
        (fun j hj => (hs.1 i j hj).2), Finset.mem_univ _, ?_⟩
    funext i
    rcases hi : s i with _ | j <;> simp [hi]
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_subtype]
  simp [aliveCount]

/--
---
conclusion: Lax470956.DynamicProgram.dp_eq_optAt
---
Lemma 6, by induction on the time index: the base case is `optAt_zero`, which realises a
state at time zero by the schedule that places exactly its occupants, and the step is
`optAt_succ`, which matches each predecessor state against the schedules extending it.
-/
theorem dp_eq_optAt (I : Instance) (t : ℕ) (s : State I) : dp I t s = optAt I t s :=
  dp_eq_optAt_aux I t s

/--
---
conclusion: Lax470956.DynamicProgram.solve_eq_optimum
---
At the horizon every job has finished, so the only reachable state is the idle one, and
the weight of the jobs started by then is the weight of the whole schedule.
-/
theorem solve_eq_optimum (I : Instance) : solve I = (optimum I : WithBot ℕ) :=
  solve_eq_optimum_aux I

/--
---
conclusion: Lax470956.DynamicProgram.card_validState_le
---
A valid state at time `t` assigns to each machine a job alive at `t`, or nothing, so the
valid states inject into the functions from machines to `Option` of the live jobs.
-/
theorem card_validState_le (I : Instance) (t : ℕ) :
    (Finset.univ.filter fun s : State I => ValidState I t s).card
      ≤ (aliveCount I t + 1) ^ I.machines :=
  card_validState_le_aux I t

end Lax470956Proofs.DynamicProgram
