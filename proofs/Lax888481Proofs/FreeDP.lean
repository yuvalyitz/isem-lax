import Lax888481.Preprocessing
import Mathlib.Tactic
import Mathlib.Data.List.Sort

/-!
The sweep, as a relation on machine configurations.

Theorem 3's algorithm records, for every machine, how long that machine has been free,
capped at `p_max`: a vector of `m` numbers each at most `p_max`. This file defines the
sweep over a list of jobs in nondecreasing order of deadline and proves it computes the
optimum — the jobs a configuration admits are exactly the jobs a schedule admits, because
a set of jobs fits on one machine exactly when, taken in deadline order, each starts after
the previous one has finished.
-/

namespace Lax888481Proofs.FreeDP

open Lax888481.Scheduling Lax888481.Scheduling.Instance
open Lax888481.DynamicProgram Lax888481.Preprocessing

variable {I : Instance}

/-! ### The Time a Machine Becomes Free -/

/-- The time at which machine `i` becomes free under `σ`: the last deadline of a job
placed on it, and `0` if there is none. -/
def freeAt (σ : I.Schedule) (i : Fin I.machines) : ℕ :=
  (Finset.univ.filter fun j => σ j = some i).sup I.d

lemma le_freeAt {σ : I.Schedule} {i : Fin I.machines} {j : Fin I.jobs} (h : σ j = some i) :
    I.d j ≤ freeAt σ i :=
  Finset.le_sup (f := I.d) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

lemma freeAt_le {σ : I.Schedule} {i : Fin I.machines} {t : ℕ}
    (h : ∀ j, σ j = some i → I.d j ≤ t) : freeAt σ i ≤ t :=
  Finset.sup_le fun j hj => h j (Finset.mem_filter.mp hj).2

@[simp] lemma freeAt_none : freeAt (fun _ => none : I.Schedule) = fun _ => 0 := by
  funext i
  exact Nat.le_zero.mp (freeAt_le fun j hj => absurd hj (by simp))

lemma freeAt_update_ne {σ : I.Schedule} {j : Fin I.jobs} {i i' : Fin I.machines}
    (hj : σ j = none) (hne : i' ≠ i) :
    freeAt (Function.update σ j (some i)) i' = freeAt σ i' := by
  unfold freeAt
  refine congrArg (fun s => Finset.sup s I.d) (Finset.filter_congr fun k _ => ?_)
  by_cases hk : k = j
  · subst hk; simp [Function.update_self, hj, Ne.symm hne]
  · simp [Function.update_of_ne hk]

lemma freeAt_update_self {σ : I.Schedule} {j : Fin I.jobs} {i : Fin I.machines}
    (hj : σ j = none) :
    freeAt (Function.update σ j (some i)) i = max (freeAt σ i) (I.d j) := by
  refine le_antisymm (Finset.sup_le fun k hk => ?_) (max_le (Finset.sup_le fun k hk => ?_) ?_)
  · have hk' : Function.update σ j (some i) k = some i := (Finset.mem_filter.mp hk).2
    by_cases hkj : k = j
    · subst hkj; exact le_max_right _ _
    · rw [Function.update_of_ne hkj] at hk'
      exact le_trans (le_freeAt hk') (le_max_left _ _)
  · have hk' : σ k = some i := (Finset.mem_filter.mp hk).2
    have hkj : k ≠ j := fun h => by rw [h, hj] at hk'; exact absurd hk' (by simp)
    exact le_freeAt (by rw [Function.update_of_ne hkj]; exact hk')
  · exact le_freeAt (by simp)

/-! ### The Sweep -/

/-- A configuration: for every machine, how long it has been free, capped at `P`. -/
abbrev St (I : Instance) : Type := Fin I.machines → ℕ

/-- Time passes: every machine has been free `δ` longer, up to the cap. -/
def adv (P δ : ℕ) (u : St I) : St I := fun i => min (u i + δ) P

/-- `Reach I P t u L u' v`: starting from configuration `u` at time `t`, the sweep may
process the jobs of `L` — each either dropped, or placed on an eligible machine that has
been free for at least its processing time — and arrive at `u'` having gained weight
`v`. -/
inductive Reach (I : Instance) (P : ℕ) : ℕ → St I → List (Fin I.jobs) → St I → ℕ → Prop
  | nil (t : ℕ) (u : St I) : Reach I P t u [] u 0
  | drop {t : ℕ} {u : St I} {j : Fin I.jobs} {L : List (Fin I.jobs)} {u' : St I} {v : ℕ} :
      Reach I P (I.d j) (adv P (I.d j - t) u) L u' v → Reach I P t u (j :: L) u' v
  | place {t : ℕ} {u : St I} {j : Fin I.jobs} {L : List (Fin I.jobs)} {u' : St I} {v : ℕ}
      (i : Fin I.machines) (hi : i ∈ I.eligible j)
      (hfree : I.p j ≤ adv P (I.d j - t) u i) :
      Reach I P (I.d j) (Function.update (adv P (I.d j - t) u) i 0) L u' v →
      Reach I P t u (j :: L) u' (v + I.w j)

/-- The weight the schedule `σ` gains on the jobs of `L`. -/
def wOn (σ : I.Schedule) (L : List (Fin I.jobs)) : ℕ :=
  (L.map fun j => (σ j).elim 0 fun _ => I.w j).sum

variable (I) in
/-- The list is in nondecreasing order of deadline. -/
abbrev Ord (L : List (Fin I.jobs)) : Prop := L.Pairwise fun a b => I.d a ≤ I.d b

/-- The configuration invariant: `u` is the clamped freedom of `σ₀` at time `t`. -/
structure Match (P t : ℕ) (u : St I) (σ₀ : I.Schedule) : Prop where
  feasible : Feasible σ₀
  le : ∀ i, freeAt σ₀ i ≤ t
  eq : ∀ i, u i = min (t - freeAt σ₀ i) P

lemma match_adv {P t : ℕ} {u : St I} {σ₀ : I.Schedule} (h : Match P t u σ₀) {t' : ℕ}
    (htt : t ≤ t') : Match P t' (adv P (t' - t) u) σ₀ where
  feasible := h.feasible
  le := fun i => le_trans (h.le i) htt
  eq := fun i => by
    have h1 := h.le i
    have h2 := h.eq i
    simp only [adv, h2]
    omega

/-! ### Placing One More Job -/

lemma feasible_update {σ : I.Schedule} {j : Fin I.jobs} {i : Fin I.machines}
    (hf : Feasible σ) (hj : σ j = none) (hi : i ∈ I.eligible j)
    (hfree : ∀ j', σ j' = some i → I.d j' ≤ I.start j) :
    Feasible (Function.update σ j (some i)) := by
  have hno : ∀ {k k' : Fin I.jobs}, k ≠ k' → σ k' = some i → I.Overlap k k' → k = j → False := by
    rintro k k' hne hk' hov rfl
    have := hfree k' hk'
    exact absurd hov.1 (by omega)
  refine ⟨fun k i' hk => ?_, fun k k' i' hne hov hk hk' => ?_⟩
  · by_cases hkj : k = j
    · subst hkj; rw [Function.update_self] at hk; cases hk; exact hi
    · rw [Function.update_of_ne hkj] at hk; exact hf.1 k i' hk
  · by_cases hkj : k = j
    · subst hkj
      rw [Function.update_self] at hk
      cases hk
      rw [Function.update_of_ne (Ne.symm hne)] at hk'
      exact hno hne hk' hov rfl
    · rw [Function.update_of_ne hkj] at hk
      by_cases hkj' : k' = j
      · subst hkj'
        rw [Function.update_self] at hk'
        cases hk'
        exact hno (Ne.symm hne) hk ⟨hov.2, hov.1⟩ rfl
      · rw [Function.update_of_ne hkj'] at hk'
        exact hf.2 k k' i' hne hov hk hk'

lemma weight_update {σ : I.Schedule} {j : Fin I.jobs} {i : Fin I.machines} (hj : σ j = none) :
    weight (Function.update σ j (some i)) = weight σ + I.w j := by
  have hpt : ∀ k, (Function.update σ j (some i) k).elim 0 (fun _ => I.w k)
      = if k = j then I.w j else (σ k).elim 0 (fun _ => I.w k) := by
    intro k
    by_cases h : k = j
    · subst h; simp
    · simp [Function.update_of_ne h, h]
  have hzero : (σ j).elim 0 (fun _ => I.w j) = 0 := by rw [hj]; rfl
  simp only [weight, hpt]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ (fun k => (σ k).elim 0 fun _ => I.w k) (Finset.mem_univ j)]
  rw [if_pos rfl, hzero]
  have : ∀ k ∈ Finset.univ.erase j,
      (if k = j then I.w j else (σ k).elim 0 fun _ => I.w k) = (σ k).elim 0 fun _ => I.w k :=
    fun k hk => if_neg (Finset.mem_erase.mp hk).1
  rw [Finset.sum_congr rfl this]
  omega

/-- The freedom test says exactly that the machine's last job has finished. -/
lemma free_iff {P t : ℕ} {u : St I} {σ₀ : I.Schedule} (h : Match P t u σ₀)
    {j : Fin I.jobs} (hP : I.p j ≤ P) (ht : t ≤ I.d j) (i : Fin I.machines) :
    I.p j ≤ adv P (I.d j - t) u i ↔ freeAt σ₀ i ≤ I.start j := by
  have h1 := (match_adv h ht).eq i
  have h2 := (match_adv h ht).le i
  have h3 : I.p j ≤ I.d j := I.p_le_d j
  have hstart : I.start j = I.d j - I.p j := rfl
  rw [h1, hstart]
  omega

/-! ### The Sweep Is Sound -/

theorem reach_sound {P : ℕ} (hP : ∀ j, I.p j ≤ P) {t : ℕ} {u : St I}
    {L : List (Fin I.jobs)} {u' : St I} {v : ℕ} (hR : Reach I P t u L u' v) :
    ∀ σ₀ : I.Schedule, Match P t u σ₀ → (∀ j ∈ L, σ₀ j = none) → (∀ j ∈ L, t ≤ I.d j) →
      Ord I L → L.Nodup →
      ∃ σ : I.Schedule, Feasible σ ∧ (∀ j, j ∉ L → σ j = σ₀ j) ∧
        weight σ = weight σ₀ + v := by
  induction hR with
  | nil t u => exact fun σ₀ h _ _ _ _ => ⟨σ₀, h.feasible, fun _ _ => rfl, by simp⟩
  | @drop t u j L u' v hR ih =>
      intro σ₀ hm hnone ht hord hnd
      have htj : t ≤ I.d j := ht j List.mem_cons_self
      obtain ⟨hhd, htl⟩ := List.pairwise_cons.mp hord
      obtain ⟨σ, hf, hag, hw⟩ := ih σ₀ (match_adv hm htj)
        (fun j' hj' => hnone j' (List.mem_cons_of_mem _ hj'))
        (fun j' hj' => hhd j' hj') htl (List.nodup_cons.mp hnd).2
      exact ⟨σ, hf, fun j' hj' => hag j' (fun hc => hj' (List.mem_cons_of_mem _ hc)), hw⟩
  | @place t u j L u' v i hi hfree hR ih =>
      intro σ₀ hm hnone ht hord hnd
      have htj : t ≤ I.d j := ht j List.mem_cons_self
      obtain ⟨hhd, htl⟩ := List.pairwise_cons.mp hord
      obtain ⟨hjnd, hndl⟩ := List.nodup_cons.mp hnd
      have hjn : σ₀ j = none := hnone j List.mem_cons_self
      have hfr : freeAt σ₀ i ≤ I.start j := (free_iff hm (hP j) htj i).mp hfree
      set σ₁ := Function.update σ₀ j (some i) with hσ₁
      have hf₁ : Feasible σ₁ :=
        feasible_update hm.feasible hjn hi fun j' hj' => le_trans (le_freeAt hj') hfr
      have hstart : I.start j ≤ I.d j := Nat.sub_le _ _
      have hm₁ : Match P (I.d j) (Function.update (adv P (I.d j - t) u) i 0) σ₁ := by
        refine ⟨hf₁, fun i' => ?_, fun i' => ?_⟩
        · by_cases hii : i' = i
          · subst hii
            rw [hσ₁, freeAt_update_self hjn]
            omega
          · rw [hσ₁, freeAt_update_ne hjn hii]
            exact le_trans (hm.le i') htj
        · by_cases hii : i' = i
          · subst hii
            rw [Function.update_self, hσ₁, freeAt_update_self hjn]
            omega
          · rw [Function.update_of_ne hii, hσ₁, freeAt_update_ne hjn hii]
            exact (match_adv hm htj).eq i'
      obtain ⟨σ, hf, hag, hw⟩ := ih σ₁ hm₁
        (fun j' hj' => by
          rw [hσ₁, Function.update_of_ne (fun hc : j' = j => hjnd (hc ▸ hj'))]
          exact hnone j' (List.mem_cons_of_mem _ hj'))
        (fun j' hj' => hhd j' hj') htl hndl
      refine ⟨σ, hf, fun j' hj' => ?_, ?_⟩
      · rw [hag j' (fun hc => hj' (List.mem_cons_of_mem _ hc)), hσ₁,
          Function.update_of_ne (fun hc : j' = j => hj' (hc ▸ List.mem_cons_self))]
      · rw [hw, hσ₁, weight_update hjn]; omega

/-! ### The Sweep Is Complete -/

@[simp] def wOn_nil (σ : I.Schedule) : wOn σ ([] : List (Fin I.jobs)) = 0 := rfl

lemma wOn_cons (σ : I.Schedule) (j : Fin I.jobs) (L : List (Fin I.jobs)) :
    wOn σ (j :: L) = (σ j).elim 0 (fun _ => I.w j) + wOn σ L := rfl

theorem reach_complete {P : ℕ} (hP : ∀ j, I.p j ≤ P) :
    ∀ (L : List (Fin I.jobs)) (t : ℕ) (u : St I) (σ₀ σ : I.Schedule),
      Match P t u σ₀ → Feasible σ → (∀ j, j ∉ L → σ j = σ₀ j) → (∀ j ∈ L, σ₀ j = none) →
      (∀ j ∈ L, t ≤ I.d j) → Ord I L → L.Nodup →
      ∃ u', Reach I P t u L u' (wOn σ L) := by
  intro L
  induction L with
  | nil => exact fun t u σ₀ σ _ _ _ _ _ _ _ => ⟨u, by simpa using Reach.nil t u⟩
  | cons j L ih =>
      intro t u σ₀ σ hm hf hag hnone ht hord hnd
      have htj : t ≤ I.d j := ht j List.mem_cons_self
      obtain ⟨hhd, htl⟩ := List.pairwise_cons.mp hord
      obtain ⟨hjnd, hndl⟩ := List.nodup_cons.mp hnd
      have hjn : σ₀ j = none := hnone j List.mem_cons_self
      rcases hj : σ j with _ | i
      · obtain ⟨u', hR⟩ := ih (I.d j) (adv P (I.d j - t) u) σ₀ σ (match_adv hm htj) hf
          (fun j' hj' => by
            by_cases hc : j' = j
            · subst hc; rw [hj, hjn]
            · exact hag j' (by simp [hc, hj']))
          (fun j' hj' => hnone j' (List.mem_cons_of_mem _ hj'))
          (fun j' hj' => hhd j' hj') htl hndl
        refine ⟨u', ?_⟩
        have hw : wOn σ (j :: L) = wOn σ L := by rw [wOn_cons, hj]; simp
        rw [hw]
        exact Reach.drop hR
      · have hi : i ∈ I.eligible j := hf.1 j i hj
        have hfr : freeAt σ₀ i ≤ I.start j := by
          refine freeAt_le fun j' hj' => ?_
          have hj'L : j' ∉ L := fun hc => by
            rw [hnone j' (List.mem_cons_of_mem _ hc)] at hj'; exact absurd hj' (by simp)
          have hj'j : j' ≠ j := fun hc => by rw [hc, hjn] at hj'; exact absurd hj' (by simp)
          have hσj' : σ j' = some i := by
            rw [hag j' (by simp [hj'j, hj'L])]; exact hj'
          have hdle : I.d j' ≤ I.d j := le_trans (le_freeAt hj') (le_trans (hm.le i) htj)
          have hpos := I.p_pos j'
          have hple := I.p_le_d j'
          by_contra hcon
          refine hf.2 j j' i (Ne.symm hj'j) ⟨by omega, ?_⟩ hj hσj'
          show I.d j' - I.p j' < I.d j
          omega
        have hfree : I.p j ≤ adv P (I.d j - t) u i := (free_iff hm (hP j) htj i).mpr hfr
        set σ₁ := Function.update σ₀ j (some i) with hσ₁
        have hf₁ : Feasible σ₁ :=
          feasible_update hm.feasible hjn hi fun j' hj' => le_trans (le_freeAt hj') hfr
        have hstart : I.start j ≤ I.d j := Nat.sub_le _ _
        have hm₁ : Match P (I.d j) (Function.update (adv P (I.d j - t) u) i 0) σ₁ := by
          refine ⟨hf₁, fun i' => ?_, fun i' => ?_⟩
          · by_cases hii : i' = i
            · subst hii; rw [hσ₁, freeAt_update_self hjn]; omega
            · rw [hσ₁, freeAt_update_ne hjn hii]; exact le_trans (hm.le i') htj
          · by_cases hii : i' = i
            · subst hii
              rw [Function.update_self, hσ₁, freeAt_update_self hjn]
              omega
            · rw [Function.update_of_ne hii, hσ₁, freeAt_update_ne hjn hii]
              exact (match_adv hm htj).eq i'
        obtain ⟨u', hR⟩ := ih (I.d j) _ σ₁ σ hm₁ hf
          (fun j' hj' => by
            by_cases hc : j' = j
            · subst hc; rw [hj, hσ₁, Function.update_self]
            · rw [hag j' (by simp [hc, hj']), hσ₁, Function.update_of_ne hc])
          (fun j' hj' => by
            rw [hσ₁, Function.update_of_ne (fun hc : j' = j => hjnd (hc ▸ hj'))]
            exact hnone j' (List.mem_cons_of_mem _ hj'))
          (fun j' hj' => hhd j' hj') htl hndl
        refine ⟨u', ?_⟩
        have : wOn σ (j :: L) = wOn σ L + I.w j := by rw [wOn_cons, hj]; simp; omega
        rw [this]
        exact Reach.place i hi hfree hR

/-! ### The Sweep Computes the Optimum of Its List -/

@[simp] lemma weight_none : weight (fun _ => none : I.Schedule) = 0 := by simp [weight]

lemma feasible_none : Feasible (fun _ => none : I.Schedule) :=
  ⟨fun j i h => absurd h (by simp), fun j j' i _ _ h => absurd h (by simp)⟩

lemma match_zero (P : ℕ) : Match P 0 (fun _ => 0) (fun _ => none : I.Schedule) where
  feasible := feasible_none
  le := by simp
  eq := by simp

lemma weight_eq_wOn {σ : I.Schedule} {L : List (Fin I.jobs)} (hnd : L.Nodup)
    (h : ∀ j, j ∉ L → σ j = none) : weight σ = wOn σ L := by
  have hsum : wOn σ L = ∑ j ∈ L.toFinset, (σ j).elim 0 fun _ => I.w j := by
    rw [wOn, ← List.sum_toFinset _ hnd]
  rw [hsum, weight]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  rw [h j (by simpa using hj)]
  rfl

/-- Membership in the set the optimum ranges over. -/
lemma mem_filter_of {σ : I.Schedule} {K : Finset (Fin I.jobs)} (hf : Feasible σ)
    (hs : ∀ j, σ j ≠ none → j ∈ K) :
    σ ∈ Finset.univ.filter fun σ : I.Schedule => Feasible σ ∧ ∀ j, σ j ≠ none → j ∈ K :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, hs⟩

lemma le_optimumOn {σ : I.Schedule} {K : Finset (Fin I.jobs)} (hf : Feasible σ)
    (hs : ∀ j, σ j ≠ none → j ∈ K) : weight σ ≤ optimumOn I K :=
  Finset.le_sup (f := weight) (mem_filter_of hf hs)

lemma exists_optimumOn (K : Finset (Fin I.jobs)) :
    ∃ σ : I.Schedule, Feasible σ ∧ (∀ j, σ j ≠ none → j ∈ K) ∧ weight σ = optimumOn I K := by
  have hne : (Finset.univ.filter fun σ : I.Schedule =>
      Feasible σ ∧ ∀ j, σ j ≠ none → j ∈ K).Nonempty :=
    ⟨fun _ => none, mem_filter_of feasible_none (by simp)⟩
  obtain ⟨σ, hmem, heq⟩ := Finset.exists_mem_eq_sup _ hne weight
  obtain ⟨-, hf, hs⟩ := Finset.mem_filter.mp hmem
  exact ⟨σ, hf, hs, heq.symm⟩

/-- **Every sweep is realised by a schedule.** -/
theorem reach_le {P : ℕ} (hP : ∀ j, I.p j ≤ P) {L : List (Fin I.jobs)} (hord : Ord I L)
    (hnd : L.Nodup) {u' : St I} {v : ℕ} (hR : Reach I P 0 (fun _ => 0) L u' v) :
    v ≤ optimumOn I L.toFinset := by
  obtain ⟨σ, hf, hag, hw⟩ :=
    reach_sound hP hR (fun _ => none) (match_zero P) (fun _ _ => rfl) (fun _ _ => Nat.zero_le _)
      hord hnd
  have : weight σ = v := by rw [hw, weight_none, Nat.zero_add]
  rw [← this]
  exact le_optimumOn hf fun j hj => by
    by_contra hc
    exact hj (hag j (by simpa using hc))

/-- **Every schedule is realised by a sweep.** -/
theorem exists_reach {P : ℕ} (hP : ∀ j, I.p j ≤ P) {L : List (Fin I.jobs)} (hord : Ord I L)
    (hnd : L.Nodup) : ∃ u', Reach I P 0 (fun _ => 0) L u' (optimumOn I L.toFinset) := by
  obtain ⟨σ, hf, hs, hw⟩ := exists_optimumOn (I := I) L.toFinset
  have hnone : ∀ j, j ∉ L → σ j = none := by
    intro j hj
    by_contra hc
    exact hj (by simpa using hs j hc)
  obtain ⟨u', hR⟩ := reach_complete hP L 0 (fun _ => 0) (fun _ => none) σ (match_zero P) hf
    (fun j hj => hnone j hj) (fun _ _ => rfl) (fun _ _ => Nat.zero_le _) hord hnd
  rw [← hw, weight_eq_wOn hnd hnone]
  exact ⟨u', hR⟩

/-! ### Jobs That Cannot Interact Are Solved Separately -/

lemma feasible_of_pointwise {σ σ' : I.Schedule} (hf : Feasible σ)
    (h : ∀ j, σ' j = σ j ∨ σ' j = none) : Feasible σ' := by
  refine ⟨fun j i hj => ?_, fun j j' i hne hov hj hj' => ?_⟩
  · rcases h j with he | he
    · exact hf.1 j i (he ▸ hj)
    · rw [he] at hj; exact absurd hj (by simp)
  · rcases h j with he | he
    · rcases h j' with he' | he'
      · exact hf.2 j j' i hne hov (he ▸ hj) (he' ▸ hj')
      · rw [he'] at hj'; exact absurd hj' (by simp)
    · rw [he] at hj; exact absurd hj (by simp)

lemma feasible_restrict {σ : I.Schedule} (hf : Feasible σ) (Q : Fin I.jobs → Prop)
    [DecidablePred Q] : Feasible (fun j => if Q j then σ j else none) := by
  refine feasible_of_pointwise hf fun j => ?_
  by_cases h : Q j <;> simp [h]

lemma weight_split (σ : I.Schedule) (Q : Fin I.jobs → Prop) [DecidablePred Q] :
    weight σ = weight (fun j => if Q j then σ j else none)
      + weight (fun j => if Q j then none else σ j) := by
  simp only [weight, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : Q j <;> simp [h]

lemma weight_congr {σ σ' : I.Schedule} (h : ∀ j, σ j = σ' j) : weight σ = weight σ' := by
  rw [funext h]

/-- **Jobs that never overlap are optimised independently.** -/
theorem optimumOn_union {A B : Finset (Fin I.jobs)} (hd : Disjoint A B)
    (hno : ∀ j ∈ A, ∀ j' ∈ B, ¬ I.Overlap j j') :
    optimumOn I (A ∪ B) = optimumOn I A + optimumOn I B := by
  refine le_antisymm ?_ ?_
  · obtain ⟨σ, hf, hs, hw⟩ := exists_optimumOn (I := I) (A ∪ B)
    rw [← hw, weight_split σ (· ∈ A)]
    refine Nat.add_le_add
      (le_optimumOn (feasible_restrict hf (· ∈ A)) fun j hj => ?_)
      (le_optimumOn (feasible_of_pointwise hf fun j => by
        by_cases h : j ∈ A <;> simp [h]) fun j hj => ?_)
    · by_contra hc; rw [if_neg hc] at hj; exact hj rfl
    · by_cases hA : j ∈ A
      · rw [if_pos hA] at hj; exact absurd rfl hj
      · rw [if_neg hA] at hj
        rcases Finset.mem_union.mp (hs j hj) with h | h
        · exact absurd h hA
        · exact h
  · obtain ⟨σA, hfA, hsA, hwA⟩ := exists_optimumOn (I := I) A
    obtain ⟨σB, hfB, hsB, hwB⟩ := exists_optimumOn (I := I) B
    have hBA : ∀ j, j ∈ A → σB j = none := by
      intro j hj
      by_contra hc
      exact (Finset.disjoint_left.mp hd hj) (hsB j hc)
    set σ : I.Schedule := fun j => if j ∈ A then σA j else σB j with hσ
    have hsupp : ∀ j i, σ j = some i → (j ∈ A ∧ σA j = some i) ∨ (j ∈ B ∧ σB j = some i) := by
      intro j i hj
      simp only [hσ] at hj
      by_cases hA : j ∈ A
      · rw [if_pos hA] at hj; exact Or.inl ⟨hA, hj⟩
      · rw [if_neg hA] at hj
        exact Or.inr ⟨hsB j (by rw [hj]; simp), hj⟩
    have hf : Feasible σ := by
      refine ⟨fun j i hj => ?_, fun j j' i hne hov hj hj' => ?_⟩
      · rcases hsupp j i hj with ⟨-, h⟩ | ⟨-, h⟩
        · exact hfA.1 j i h
        · exact hfB.1 j i h
      · rcases hsupp j i hj with ⟨hjA, hjs⟩ | ⟨hjB, hjs⟩
        · rcases hsupp j' i hj' with ⟨-, h'⟩ | ⟨hj'B, -⟩
          · exact hfA.2 j j' i hne hov hjs h'
          · exact hno j hjA j' hj'B hov
        · rcases hsupp j' i hj' with ⟨hj'A, -⟩ | ⟨-, h'⟩
          · exact hno j' hj'A j hjB ⟨hov.2, hov.1⟩
          · exact hfB.2 j j' i hne hov hjs h'
    have hwsplit : weight σ = weight σA + weight σB := by
      rw [weight_split σ (· ∈ A)]
      congr 1
      · refine weight_congr fun j => ?_
        by_cases hA : j ∈ A
        · simp [hσ, hA]
        · rw [if_neg hA]
          by_contra hc
          exact hc (by_contra fun h => hc (by
            rcases hj : σA j with _ | i
            · exact (hj ▸ rfl : σA j = none) ▸ rfl
            · exact absurd (hsA j (by rw [hj]; simp)) hA))
      · refine weight_congr fun j => ?_
        by_cases hA : j ∈ A
        · rw [if_pos hA, hBA j hA]
        · simp [hσ, hA]
    rw [← hwA, ← hwB, ← hwsplit]
    exact le_optimumOn hf fun j hj => by
      rcases Option.ne_none_iff_exists'.mp hj with ⟨i, hi⟩
      rcases hsupp j i hi with ⟨h, -⟩ | ⟨h, -⟩
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h

/-- Nothing may be scheduled, so nothing is earned. -/
lemma optimumOn_empty : optimumOn I (∅ : Finset (Fin I.jobs)) = 0 := by
  obtain ⟨σ, -, hs, hw⟩ := exists_optimumOn (I := I) ∅
  have hσ : σ = fun _ => none := funext fun j => by
    by_contra hc
    exact absurd (hs j hc) (by simp)
  rw [← hw, hσ, weight_none]

end Lax888481Proofs.FreeDP
