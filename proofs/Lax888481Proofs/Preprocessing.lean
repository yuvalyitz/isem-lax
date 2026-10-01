import Lax888481.Preprocessing
import Lax888481Proofs.DynamicProgram

/-!
Lemma 5 and Observation 5: the preprocessing step does not change the optimum, and after
it only a bounded number of jobs are alive at any instant.

Lemma 5 is an exchange argument run to exhaustion. `exists_kept_substitute` says that a
scheduled but discarded job always has a kept, unscheduled job with the same interval
that is eligible on the same machine and at least as heavy — because the machine keeps
the `m` best of that interval and a schedule occupies it with at most one at a time.
`swapSched` performs the exchange, `badSet` counts the jobs still to be exchanged, and
`exists_on_keep` is the induction on that count.

Observation 5 is a counting argument: a job alive at `t` has its deadline in one of
`p_max` positions and its processing time in one of `p_max`, and each of the resulting
intervals keeps at most `m` jobs on each of the `m` machines.
-/

namespace Lax888481Proofs.Preprocessing

open Lax888481.Scheduling Lax888481.Scheduling.Instance Lax888481.DynamicProgram Lax888481.Preprocessing Lax888481Proofs.DynamicProgram

variable (I : Instance)

variable {I}

lemma better_w_le {j j' : Fin I.jobs} (h : Better I j j') : I.w j' ≤ I.w j := by
  rcases h with h | ⟨h, -⟩ <;> omega

lemma better_irrefl (j : Fin I.jobs) : ¬ Better I j j := by
  rintro (h | ⟨-, h⟩) <;> omega

lemma better_trans {a b c : Fin I.jobs} (h1 : Better I a b) (h2 : Better I b c) : Better I a c := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, by omega⟩

lemma better_total {a b : Fin I.jobs} (h : a ≠ b) : Better I a b ∨ Better I b a := by
  rcases Nat.lt_trichotomy (I.w a) (I.w b) with hw | hw | hw
  · exact Or.inr (Or.inl hw)
  · rcases Nat.lt_trichotomy (a : ℕ) (b : ℕ) with hr | hr | hr
    · exact Or.inl (Or.inr ⟨hw.symm, hr⟩)
    · exact absurd (Fin.ext hr) h
    · exact Or.inr (Or.inr ⟨hw, hr⟩)
  · exact Or.inl (Or.inl hw)

variable (I)

variable {I}

lemma mem_sameSlot {i : Fin I.machines} {j j' : Fin I.jobs} :
    j' ∈ sameSlot I i j ↔ I.d j' = I.d j ∧ I.p j' = I.p j ∧ i ∈ I.eligible j' := by
  rw [sameSlot, slotOf]; simp

lemma self_mem_sameSlot {i : Fin I.machines} {j : Fin I.jobs} (h : i ∈ I.eligible j) :
    j ∈ sameSlot I i j := mem_sameSlot.mpr ⟨rfl, rfl, h⟩

/-- Members of a slot have that same slot. -/
lemma sameSlot_congr {i : Fin I.machines} {j j' : Fin I.jobs} (h : j' ∈ sameSlot I i j) :
    sameSlot I i j' = sameSlot I i j := by
  obtain ⟨hd, hp, -⟩ := mem_sameSlot.mp h
  ext j''
  simp only [mem_sameSlot, hd, hp]

/-- Jobs sharing a slot are `π`-ordered by their rank. -/
lemma rank_lt_rank {i : Fin I.machines} {j a b : Fin I.jobs}
    (ha : a ∈ sameSlot I i j) (hb : b ∈ sameSlot I i j) (hab : Better I a b) :
    rank I i a < rank I i b := by
  rw [rank, rank, sameSlot_congr ha, sameSlot_congr hb]
  refine Finset.card_lt_card ⟨fun x hx => ?_, ?_⟩
  · simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, better_trans hx.2 hab⟩
  · intro hsub
    have : a ∈ (sameSlot I i j).filter (fun x => Better I x a) :=
      hsub (Finset.mem_filter.mpr ⟨ha, hab⟩)
    exact better_irrefl a (Finset.mem_filter.mp this).2

lemma rank_inj_on {i : Fin I.machines} {j a b : Fin I.jobs}
    (ha : a ∈ sameSlot I i j) (hb : b ∈ sameSlot I i j) (h : rank I i a = rank I i b) :
    a = b := by
  by_contra hne
  rcases better_total hne with hab | hab
  · exact absurd h (Nat.ne_of_lt (rank_lt_rank ha hb hab))
  · exact absurd h.symm (Nat.ne_of_lt (rank_lt_rank hb ha hab))

lemma better_of_rank_lt {i : Fin I.machines} {j a b : Fin I.jobs}
    (ha : a ∈ sameSlot I i j) (hb : b ∈ sameSlot I i j) (h : rank I i a < rank I i b) :
    Better I a b := by
  rcases eq_or_ne a b with rfl | hne
  · omega
  rcases better_total hne with hab | hab
  · exact hab
  · exact absurd (rank_lt_rank hb ha hab) (by omega)

/-! ## 3. There is always a kept, unscheduled substitute -/

lemma conflict_of_same_interval {a b : Fin I.jobs} (hd : I.d a = I.d b) (hp : I.p a = I.p b) :
    I.Overlap a b := by
  have h1 := I.p_pos a
  have h2 := I.p_le_d a
  constructor <;> · change I.d _ - I.p _ < I.d _; omega

lemma rank_lt_card {i : Fin I.machines} {j a : Fin I.jobs} (ha : a ∈ sameSlot I i j) :
    rank I i a < (sameSlot I i j).card := by
  rw [rank, sameSlot_congr ha]
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, ?_⟩
  intro hsub
  exact better_irrefl a (Finset.mem_filter.mp (hsub ha)).2

lemma exists_rank_eq {i : Fin I.machines} {j : Fin I.jobs} (v : ℕ) (hv : v < (sameSlot I i j).card) :
    ∃ a ∈ sameSlot I i j, rank I i a = v := by
  obtain ⟨a, ha, hav⟩ := Finset.surj_on_of_inj_on_of_card_le
    (f := fun (a : Fin I.jobs) (_ : a ∈ sameSlot I i j) => rank I i a)
    (fun a ha => Finset.mem_range.mpr (rank_lt_card ha))
    (fun a b ha hb h => rank_inj_on ha hb h) (by simp) v (Finset.mem_range.mpr hv)
  exact ⟨a, ha, hav.symm⟩

/-- If `j` is not among the `m` best of its slot on `i`, then the `m` best of that slot
all exist, are kept, and beat `j`. -/
lemma card_top_ge {i : Fin I.machines} {j : Fin I.jobs} (hj : i ∈ I.eligible j)
    (hm : I.machines ≤ rank I i j) :
    I.machines
      ≤ ((sameSlot I i j).filter (fun a => rank I i a < I.machines)).card := by
  have hjc := rank_lt_card (self_mem_sameSlot hj)
  have hsub : Finset.range I.machines
      ⊆ ((sameSlot I i j).filter (fun a => rank I i a < I.machines)).image (rank I i) := by
    intro v hv
    rw [Finset.mem_range] at hv
    obtain ⟨a, ha, hav⟩ := exists_rank_eq (i := i) (j := j) v (by omega)
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, by omega⟩, hav⟩
  calc I.machines = (Finset.range I.machines).card := by simp
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le

/-- **The substitution step.** A scheduled job that Construction 3 discards can be
replaced by an unscheduled job of the same interval, on the same machine, of at least
the same weight, that Construction 3 keeps. -/
theorem exists_kept_substitute {σ : I.Schedule} (hfeas : Feasible σ) {j : Fin I.jobs}
    {i : Fin I.machines} (hσ : σ j = some i) (hbad : j ∉ keep I) :
    ∃ j', j' ∈ keep I ∧ σ j' = none ∧ I.d j' = I.d j ∧ I.p j' = I.p j ∧ i ∈ I.eligible j'
      ∧ I.w j ≤ I.w j' := by
  have helig : i ∈ I.eligible j := hfeas.1 j i hσ
  have hm : I.machines ≤ rank I i j := by
    by_contra hlt
    exact hbad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, helig, by omega⟩⟩)
  set T := (sameSlot I i j).filter (fun a => rank I i a < I.machines) with hT
  have hTcard : I.machines ≤ T.card := card_top_ge helig hm
  have hTslot : ∀ a ∈ T, a ∈ sameSlot I i j := fun a ha => (Finset.mem_filter.mp ha).1
  have hTkeep : ∀ a ∈ T, a ∈ keep I := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨-, -, he⟩ := mem_sameSlot.mp ha1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, he, ha2⟩⟩
  have hTbetter : ∀ a ∈ T, Better I a j := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    exact better_of_rank_lt ha1 (self_mem_sameSlot helig) (by omega)
  -- at most `m - 1` members of `T` are scheduled, because `j` occupies machine `i`
  set Tsch := T.filter (fun a => σ a ≠ none) with hTs
  have hTsch : Tsch.card ≤ (Finset.univ.erase i).card := by
    refine Finset.card_le_card_of_injOn (fun a => (σ a).getD i) ?_ ?_
    · intro a ha
      obtain ⟨haT, hane⟩ := Finset.mem_filter.mp ha
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hane
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      change (σ a).getD i ≠ i
      rw [hk]
      intro hki
      simp only [Option.getD_some] at hki
      obtain ⟨hd, hp, -⟩ := mem_sameSlot.mp (hTslot a haT)
      have hane' : a ≠ j := fun hc => better_irrefl j (hc ▸ hTbetter a haT)
      refine hfeas.2 a j i hane' (conflict_of_same_interval hd hp) ?_ hσ
      rw [hk, hki]
    · intro a ha b hb hab
      have ha' : a ∈ T.filter (fun x => σ x ≠ none) := by rw [← hTs]; simpa using ha
      have hb' : b ∈ T.filter (fun x => σ x ≠ none) := by rw [← hTs]; simpa using hb
      obtain ⟨haT, hane⟩ := Finset.mem_filter.mp ha'
      obtain ⟨hbT, hbne⟩ := Finset.mem_filter.mp hb'
      obtain ⟨ka, hka⟩ := Option.ne_none_iff_exists'.mp hane
      obtain ⟨kb, hkb⟩ := Option.ne_none_iff_exists'.mp hbne
      simp only [hka, hkb, Option.getD_some] at hab
      subst hab
      by_contra hne
      obtain ⟨hda, hpa, -⟩ := mem_sameSlot.mp (hTslot a haT)
      obtain ⟨hdb, hpb, -⟩ := mem_sameSlot.mp (hTslot b hbT)
      exact hfeas.2 a b ka hne (conflict_of_same_interval (by omega) (by omega)) hka hkb
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at hTsch
  have hmpos : 0 < I.machines := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hlt : Tsch.card < T.card := by omega
  obtain ⟨a, haT, haTs⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have ha0 : σ a = none := by
    by_contra hc
    exact haTs (Finset.mem_filter.mpr ⟨haT, hc⟩)
  obtain ⟨hd, hp, he⟩ := mem_sameSlot.mp (hTslot a haT)
  exact ⟨a, hTkeep a haT, ha0, hd, hp, he, better_w_le (hTbetter a haT)⟩

/-! ## 4. Lemma 5: preprocessing does not change the optimum -/

lemma conflict_congr_left {a a' b : Fin I.jobs} (hd : I.d a' = I.d a) (hp : I.p a' = I.p a) :
    I.Overlap a' b ↔ I.Overlap a b := by
  simp only [Instance.Overlap, Instance.start, hd, hp]

/-- Replace `j` by `j'` on machine `i`. -/
def swapSched (σ : I.Schedule) (j j' : Fin I.jobs) (i : Fin I.machines) : I.Schedule := fun x =>
  if x = j then none else if x = j' then some i else σ x

section Swap

variable {σ : I.Schedule} {j j' : Fin I.jobs} {i : Fin I.machines}
  (hfeas : Feasible σ) (hσ : σ j = some i) (h0 : σ j' = none)
  (hd : I.d j' = I.d j) (hp : I.p j' = I.p j) (he : i ∈ I.eligible j') (hne : j ≠ j')

@[simp] lemma swapSched_self : swapSched σ j j' i j = none := by simp [swapSched]

include hne in
@[simp] lemma swapSched_new : swapSched σ j j' i j' = some i := by
  simp [swapSched, Ne.symm hne]

lemma swapSched_other {x : Fin I.jobs} (h1 : x ≠ j) (h2 : x ≠ j') :
    swapSched σ j j' i x = σ x := by simp [swapSched, h1, h2]

include hfeas hσ h0 hd hp he hne in
theorem swap_feasible : Feasible (swapSched σ j j' i) := by
  constructor
  · intro x k hx
    by_cases h1 : x = j
    · rw [h1, swapSched_self] at hx; exact absurd hx (by simp)
    by_cases h2 : x = j'
    · rw [h2, swapSched_new hne] at hx
      rw [h2, ← Option.some.inj hx]
      exact he
    · rw [swapSched_other h1 h2] at hx
      exact hfeas.1 x k hx
  · intro x y k hxy hconf hx hy
    by_cases h1 : x = j
    · rw [h1, swapSched_self] at hx; exact absurd hx (by simp)
    by_cases h1' : y = j
    · rw [h1', swapSched_self] at hy; exact absurd hy (by simp)
    by_cases h2 : x = j'
    · subst h2
      rw [swapSched_new hne] at hx
      have hy2 : y ≠ x := fun hc => hxy hc.symm
      rw [swapSched_other h1' hy2] at hy
      have hk : i = k := Option.some.inj hx
      subst hk
      exact hfeas.2 j y i (fun hc => h1' hc.symm)
        ((conflict_congr_left hd hp).mp hconf) hσ hy
    by_cases h2' : y = j'
    · subst h2'
      rw [swapSched_new hne] at hy
      rw [swapSched_other h1 h2] at hx
      have hk : i = k := Option.some.inj hy
      subst hk
      have hcj : I.Overlap x j :=
        overlap_symm I ((conflict_congr_left hd hp).mp (overlap_symm I hconf))
      exact hfeas.2 x j i h1 hcj hx hσ
    · rw [swapSched_other h1 h2] at hx
      rw [swapSched_other h1' h2'] at hy
      exact hfeas.2 x y k hxy hconf hx hy

include hσ h0 hne in
theorem swap_weight :
    weight σ + I.w j' = weight (swapSched σ j j' i) + I.w j := by
  have hj' : j' ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j'⟩
  have hsplit : ∀ f : Fin I.jobs → ℕ,
      ∑ x, f x = f j + (f j' + ∑ x ∈ (Finset.univ.erase j).erase j', f x) := by
    intro f
    rw [← Finset.add_sum_erase _ f (Finset.mem_univ j), ← Finset.add_sum_erase _ f hj']
  have hrest : ∑ x ∈ (Finset.univ.erase j).erase j',
        (σ x).elim 0 (fun _ => I.w x)
      = ∑ x ∈ (Finset.univ.erase j).erase j',
        (swapSched σ j j' i x).elim 0 (fun _ => I.w x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hx2, hx1⟩ := Finset.mem_erase.mp hx
    rw [swapSched_other (Finset.mem_erase.mp hx1).1 hx2]
  rw [weight, weight, hsplit (fun x => (σ x).elim 0 (fun _ => I.w x)),
    hsplit (fun x => (swapSched σ j j' i x).elim 0 (fun _ => I.w x))]
  rw [hσ, h0, swapSched_self, swapSched_new hne, ← hrest]
  simp only [Option.elim]
  omega

end Swap

variable (I)

/-- The scheduled jobs that Construction 3 discards. -/
noncomputable def badSet (σ : I.Schedule) : Finset (Fin I.jobs) :=
  Finset.univ.filter (fun x => σ x ≠ none ∧ x ∉ keep I)

variable {I}

lemma badSet_swap {σ : I.Schedule} {j j' : Fin I.jobs} {i : Fin I.machines}
    (hne : j ≠ j') (hj' : j' ∈ keep I) :
    badSet I (swapSched σ j j' i) ⊆ (badSet I σ).erase j := by
  intro x hx
  simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxj : x ≠ j := by rintro rfl; rw [swapSched_self] at hx1; exact hx1 rfl
  have hxj' : x ≠ j' := by rintro rfl; exact hx2 hj'
  rw [swapSched_other hxj hxj'] at hx1
  exact Finset.mem_erase.mpr ⟨hxj, by
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hx1, hx2⟩⟩

/-- Any feasible schedule can be improved to one using only the kept jobs. -/
theorem exists_on_keep : ∀ (n : ℕ) (σ : I.Schedule), Feasible σ →
    (badSet I σ).card ≤ n →
    ∃ σ', Feasible σ' ∧ (∀ x, σ' x ≠ none → x ∈ keep I) ∧ weight σ ≤ weight σ' := by
  intro n
  induction n with
  | zero =>
      intro σ hfeas hcard
      refine ⟨σ, hfeas, fun x hx => ?_, le_rfl⟩
      by_contra hkeep
      have : x ∈ badSet I σ := by
        simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hx, hkeep⟩
      have := Finset.card_pos.mpr ⟨x, this⟩
      omega
  | succ n ih =>
      intro σ hfeas hcard
      rcases Finset.eq_empty_or_nonempty (badSet I σ) with hemp | ⟨j, hj⟩
      · refine ⟨σ, hfeas, fun x hx => ?_, le_rfl⟩
        by_contra hkeep
        have : x ∈ badSet I σ := by
          simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hx, hkeep⟩
        rw [hemp] at this
        exact absurd this (by simp)
      · simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨hjs, hjk⟩ := hj
        obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hjs
        obtain ⟨j', hj'keep, hj'0, hd, hp, he, hw⟩ := exists_kept_substitute hfeas hi hjk
        have hne : j ≠ j' := by rintro rfl; exact hjk hj'keep
        have hfe := swap_feasible hfeas hi hj'0 hd hp he hne
        have hwe := swap_weight (i := i) hi hj'0 hne
        have hbad : (badSet I (swapSched σ j j' i)).card ≤ n := by
          have hsub := badSet_swap (σ := σ) (i := i) hne hj'keep
          have h1 : (badSet I σ).card ≠ 0 := by
            intro hc
            have : j ∈ badSet I σ := by
              simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hjs, hjk⟩
            have := Finset.card_pos.mpr ⟨j, this⟩
            omega
          have h2 : ((badSet I σ).erase j).card = (badSet I σ).card - 1 := by
            refine Finset.card_erase_of_mem ?_
            simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hjs, hjk⟩
          have := Finset.card_le_card hsub
          omega
        obtain ⟨σ'', hf'', hk'', hw''⟩ := ih (swapSched σ j j' i) hfe hbad
        exact ⟨σ'', hf'', hk'', by omega⟩

/-- **Lemma 5.** Construction 3 preserves the optimum. -/
theorem optimumOn_keep_aux : optimumOn I (keep I) = optimum I := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le fun σ hσ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact Finset.le_sup (f := weight) (by simpa using hσ.1)
  · refine Finset.sup_le fun σ hσ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨σ', hf', hk', hw'⟩ := exists_on_keep (badSet I σ).card σ hσ le_rfl
    refine le_trans hw' (Finset.le_sup (f := weight) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hf', hk'⟩

lemma p_le_pmax (j : Fin I.jobs) : I.p j ≤ I.pmax := Finset.le_sup (Finset.mem_univ j)

lemma mem_slotOf {i : Fin I.machines} {dd pp : ℕ} {j : Fin I.jobs} :
    j ∈ slotOf I i dd pp ↔ I.d j = dd ∧ I.p j = pp ∧ i ∈ I.eligible j := by
  rw [slotOf]; simp

/-- At most `m` jobs of any one slot survive Construction 3 on a given machine. -/
lemma card_top_le (i : Fin I.machines) (dd pp : ℕ) :
    ((slotOf I i dd pp).filter (fun a => rank I i a < I.machines)).card
      ≤ I.machines := by
  refine le_trans (Finset.card_le_card_of_injOn (rank I i) ?_ ?_)
    (le_of_eq (Finset.card_range _))
  · intro a ha
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    obtain ⟨hda, hpa, hea⟩ := mem_slotOf.mp ha.1
    obtain ⟨hdb, hpb, heb⟩ := mem_slotOf.mp hb.1
    refine rank_inj_on (j := a) (self_mem_sameSlot hea) ?_ hab
    exact mem_sameSlot.mpr ⟨by omega, by omega, heb⟩

/-- At most `m²` kept jobs share one interval. -/
lemma card_keep_slot_le (dd pp : ℕ) :
    ((keep I).filter (fun j => I.d j = dd ∧ I.p j = pp)).card
      ≤ I.machines * I.machines := by
  have hsub : (keep I).filter (fun j => I.d j = dd ∧ I.p j = pp)
      ⊆ Finset.univ.biUnion
        (fun i : Fin I.machines => (slotOf I i dd pp).filter
          (fun a => rank I i a < I.machines)) := by
    intro j hj
    simp only [Finset.mem_filter] at hj
    obtain ⟨hjk, hjd, hjp⟩ := hj
    obtain ⟨-, i, hi, hr⟩ := Finset.mem_filter.mp hjk
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨mem_slotOf.mpr ⟨hjd, hjp, hi⟩, hr⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  refine le_trans (Finset.sum_le_sum (fun i _ => card_top_le i dd pp)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Observation 5.** After Construction 3, at most `p_max² · m²` jobs are alive at any
one instant — a bound in `m` and `p_max` alone, with no dependence on `n`. Combined with
`Instance.card_validState_le` this makes the dynamic program fixed-parameter
tractable for the combined parameter. -/
theorem card_keep_alive_le_aux (k : ℕ) :
    ((keep I).filter (fun j => Active k j)).card
      ≤ I.pmax * I.pmax * (I.machines * I.machines) := by
  classical
  set D : Finset (ℕ × ℕ) := Finset.Icc (k + 1) (k + I.pmax) ×ˢ Finset.Icc 1 I.pmax with hD
  have hsub : (keep I).filter (fun j => Active k j)
      ⊆ D.biUnion (fun q => (keep I).filter (fun j => I.d j = q.1 ∧ I.p j = q.2)) := by
    intro j hj
    simp only [Finset.mem_filter] at hj
    obtain ⟨hjk, hact⟩ := hj
    obtain ⟨ha1, ha2⟩ := hact
    have hst : I.d j - I.p j ≤ k := ha1
    have hp1 := I.p_pos j
    have hp2 := I.p_le_d j
    have hpm := p_le_pmax j
    refine Finset.mem_biUnion.mpr ⟨(I.d j, I.p j), ?_, ?_⟩
    · rw [hD, Finset.mem_product]
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_Icc.mpr ⟨by omega, hpm⟩⟩
    · exact Finset.mem_filter.mpr ⟨hjk, rfl, rfl⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  have hbound : ∀ q ∈ D,
      ((keep I).filter (fun j => I.d j = q.1 ∧ I.p j = q.2)).card
        ≤ I.machines * I.machines := fun q _ => card_keep_slot_le q.1 q.2
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  rw [hD, Finset.card_product, Nat.card_Icc, Nat.card_Icc]
  have h1 : k + I.pmax + 1 - (k + 1) = I.pmax := by omega
  have h2 : I.pmax + 1 - 1 = I.pmax := by omega
  rw [h1, h2]

/--
---
conclusion: Lax888481.Preprocessing.optimumOn_keep
---
One inequality is immediate, since a schedule using only kept jobs is a schedule. The
other is the exchange argument: any feasible schedule can be rewritten, one discarded
job at a time, into one of no smaller weight that uses only kept jobs.
-/
theorem optimumOn_keep (I : Instance) : optimumOn I (keep I) = optimum I :=
  optimumOn_keep_aux (I := I)

/--
---
conclusion: Lax888481.Preprocessing.card_keep_alive_le
---
The kept jobs alive at `t` are covered by the intervals `[dd - pp, dd)` with
`dd ∈ (t, t + p_max]` and `pp ∈ [1, p_max]`, and each such interval keeps at most
`m` jobs per machine.
-/
theorem card_keep_alive_le (I : Instance) (t : ℕ) :
    ((keep I).filter fun j => Active t j).card
      ≤ I.pmax * I.pmax * (I.machines * I.machines) :=
  card_keep_alive_le_aux (I := I) t

end Lax888481Proofs.Preprocessing
