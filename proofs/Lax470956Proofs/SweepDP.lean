import Lax470956Proofs.SweepTable

/-!
The sweep's table, against the sweep relation.

The program's table is indexed by the numbers of configurations; `FreeDP.Reach` speaks of
configurations. This file is the dictionary between them, and it shows that the two table
passes the program makes — letting time run, and placing a job — are the two moves of the
relation.
-/

namespace Lax470956Proofs.SweepDP

open Lax470956.Scheduling Lax470956.Scheduling.Instance
open Lax470956Proofs.FreeDP Lax470956Proofs.SweepTable

variable {I : Instance} {P : ℕ}

/-- The number of a configuration. -/
def codeOf (P : ℕ) (I : Instance) (u : St I) : ℕ :=
  Radix.enc P I.machines fun i => if h : i < I.machines then u ⟨i, h⟩ else 0

/-- The configuration of a number. -/
def stOf (P : ℕ) (I : Instance) (c : ℕ) : St I := fun i => Radix.dig P c i.val

lemma codeOf_lt {u : St I} (hu : ∀ i, u i ≤ P) :
    codeOf P I u < (P + 1) ^ I.machines := by
  refine Radix.enc_lt fun i hi => ?_
  rw [dif_pos hi]
  exact hu _

lemma dig_codeOf {u : St I} (hu : ∀ i, u i ≤ P) (i : Fin I.machines) :
    Radix.dig P (codeOf P I u) i.val = u i := by
  rw [codeOf, Radix.dig_enc (fun k hk => by rw [dif_pos hk]; exact hu _) i.val i.isLt,
    dif_pos i.isLt]

lemma stOf_codeOf {u : St I} (hu : ∀ i, u i ≤ P) : stOf P I (codeOf P I u) = u := by
  funext i; exact dig_codeOf hu i

lemma codeOf_stOf {c : ℕ} (hc : c < (P + 1) ^ I.machines) :
    codeOf P I (stOf P I c) = c := by
  rw [codeOf, Radix.enc_congr (v := Radix.dig P c) fun i hi => by rw [dif_pos hi]; rfl]
  exact Radix.enc_dig c hc

lemma stOf_le (c : ℕ) (i : Fin I.machines) : stOf P I c i ≤ P := Radix.dig_le _ _

lemma advOf_codeOf (δ : ℕ) {u : St I} (hu : ∀ i, u i ≤ P) :
    advOf P I.machines δ (codeOf P I u) = codeOf P I (adv P δ u) := by
  unfold advOf codeOf
  refine Radix.enc_congr fun i hi => ?_
  rw [dif_pos hi, Radix.dig_enc (fun k hk => by rw [dif_pos hk]; exact hu _) i hi, dif_pos hi]
  rfl

lemma zeroAt_codeOf (i : Fin I.machines) {u : St I} (hu : ∀ k, u k ≤ P) :
    zeroAt P i.val (codeOf P I u) = codeOf P I (Function.update u i 0) := by
  have hdg : Radix.dig P (codeOf P I u) i.val = u i := dig_codeOf hu i
  unfold zeroAt
  rw [hdg]
  unfold codeOf
  have hup : ∀ k, k < I.machines →
      (if h : k < I.machines then Function.update u i 0 ⟨k, h⟩ else 0)
        = Function.update (fun k => if h : k < I.machines then u ⟨k, h⟩ else 0) i.val 0 k := by
    intro k hk
    rw [dif_pos hk]
    by_cases hki : k = i.val
    · rw [show (⟨k, hk⟩ : Fin I.machines) = i from Fin.ext hki, Function.update_self, hki,
        Function.update_self]
    · rw [Function.update_of_ne hki, dif_pos hk, Function.update_of_ne (by
        intro hc; exact hki (congrArg Fin.val hc))]
  rw [Radix.enc_congr hup,
    Radix.enc_update_zero (fun k hk => by rw [dif_pos hk]; exact hu _) i.isLt, dif_pos i.isLt]

/-! ### One job of the sweep -/

/-- The sweep's move on one job, from reference `t`. -/
inductive Step1 (I : Instance) (P : ℕ) (t : ℕ) (u : St I) (j : Fin I.jobs) : St I → ℕ → Prop
  | drop : Step1 I P t u j (adv P (I.d j - t) u) 0
  | place (i : Fin I.machines) (hi : i ∈ I.eligible j)
      (hfree : I.p j ≤ adv P (I.d j - t) u i) :
      Step1 I P t u j (Function.update (adv P (I.d j - t) u) i 0) (I.w j)

/-- The reference time after a list has been processed from `t`. -/
def refOf (I : Instance) (t : ℕ) (L : List (Fin I.jobs)) : ℕ := (L.getLast?).elim t I.d

@[simp] def refOf_nil (I : Instance) (t : ℕ) : refOf I t [] = t := rfl

lemma refOf_snoc (I : Instance) (t : ℕ) (L : List (Fin I.jobs)) (j : Fin I.jobs) :
    refOf I t (L ++ [j]) = I.d j := by simp [refOf]

lemma reach_cons_iff {t : ℕ} {u : St I} {j : Fin I.jobs} {L : List (Fin I.jobs)}
    {u' : St I} {v : ℕ} :
    Reach I P t u (j :: L) u' v ↔
      ∃ u1 v1 v2, Step1 I P t u j u1 v1 ∧ Reach I P (I.d j) u1 L u' v2 ∧ v = v1 + v2 := by
  constructor
  · intro h
    cases h with
    | drop h => exact ⟨_, 0, _, Step1.drop, h, by omega⟩
    | place i hi hfree h => exact ⟨_, I.w j, _, Step1.place i hi hfree, h, by omega⟩
  · rintro ⟨u1, v1, v2, hs, hr, rfl⟩
    cases hs with
    | drop => simpa using Reach.drop hr
    | place i hi hfree =>
        have : I.w j + v2 = v2 + I.w j := by omega
        rw [this]
        exact Reach.place i hi hfree hr

lemma reach_snoc_iff {t : ℕ} {u : St I} {L : List (Fin I.jobs)} {j : Fin I.jobs}
    {u'' : St I} {v : ℕ} :
    Reach I P t u (L ++ [j]) u'' v ↔
      ∃ u' v1 v2, Reach I P t u L u' v1 ∧ Step1 I P (refOf I t L) u' j u'' v2 ∧
        v = v1 + v2 := by
  induction L generalizing t u v with
  | nil =>
      simp only [List.nil_append, refOf_nil]
      rw [reach_cons_iff]
      constructor
      · rintro ⟨u1, v1, v2, hs, hr, rfl⟩
        cases hr
        exact ⟨u, 0, v1, Reach.nil t u, hs, by omega⟩
      · rintro ⟨u', v1, v2, hr, hs, rfl⟩
        cases hr
        exact ⟨u'', v2, 0, hs, Reach.nil _ _, by omega⟩
  | cons a L ih =>
      simp only [List.cons_append]
      rw [reach_cons_iff]
      have hrefc : refOf I t (a :: L) = refOf I (I.d a) L := by
        cases L with
        | nil => simp [refOf]
        | cons b L' =>
            unfold refOf
            rw [List.getLast?_cons_cons]
            rcases hg : (b :: L').getLast? with _ | g
            · exact absurd hg (by simp)
            · rfl
      rw [hrefc]
      constructor
      · rintro ⟨u1, v1, v2, hs, hr, rfl⟩
        obtain ⟨u', w1, w2, hr1, hs2, rfl⟩ := ih.mp hr
        exact ⟨u', v1 + w1, w2, reach_cons_iff.mpr ⟨u1, v1, w1, hs, hr1, rfl⟩, hs2, by omega⟩
      · rintro ⟨u', v1, v2, hrc, hs2, rfl⟩
        obtain ⟨u1, w1, w2, hs, hr1, rfl⟩ := reach_cons_iff.mp hrc
        exact ⟨u1, w1, w2 + v2, hs, ih.mpr ⟨u', w2, v2, hr1, hs2, rfl⟩, by omega⟩

/-! ### What the table holds -/

lemma adv_adv (P a b : ℕ) (u : St I) : adv P a (adv P b u) = adv P (a + b) u := by
  funext i; simp only [adv]; omega

lemma adv_zero {u : St I} (hu : ∀ i, u i ≤ P) : adv P 0 u = u := by
  funext i; simp only [adv]; have := hu i; omega

theorem reach_bounded : ∀ {t : ℕ} {u : St I} {L : List (Fin I.jobs)} {u' : St I} {v : ℕ},
    Reach I P t u L u' v → (∀ i, u i ≤ P) → ∀ i, u' i ≤ P
  | _, _, _, _, _, .nil _ _, hu => hu
  | _, _, _, _, _, .drop h, _ => reach_bounded h fun i => by simp [adv]
  | _, _, _, _, _, .place i _ _ h, _ => reach_bounded h fun k => by
      by_cases hk : k = i
      · subst hk; simp
      · rw [Function.update_of_ne hk]; simp [adv]

/-- The configurations the sweep can be in after `L`, seen at time `t`. -/
def ReachAt (I : Instance) (P : ℕ) (L : List (Fin I.jobs)) (t : ℕ) (u : St I) (v : ℕ) : Prop :=
  ∃ u0, Reach I P 0 (fun _ => 0) L u0 v ∧ u = adv P (t - refOf I 0 L) u0

lemma reachAt_le {L : List (Fin I.jobs)} {t : ℕ} {u : St I} {v : ℕ}
    (h : ReachAt I P L t u v) : ∀ i, u i ≤ P := by
  obtain ⟨u0, -, rfl⟩ := h
  intro i; simp [adv]

/-- The table the sweep holds: `1 + v` capped at the number of each configuration it can
be in with best weight `v`, and `0` elsewhere. -/
structure Tab (C : ℕ) (L : List (Fin I.jobs)) (t : ℕ) (T : ℕ → ℕ) : Prop where
  cap : ∀ c, T c ≤ C + 1
  out : ∀ c, (P + 1) ^ I.machines ≤ c → T c = 0
  ge : ∀ u v, ReachAt I P L t u v → min v C + 1 ≤ T (codeOf P I u)
  le : ∀ u, (∀ i, u i ≤ P) → T (codeOf P I u) ≠ 0 →
    ∃ v, ReachAt I P L t u v ∧ T (codeOf P I u) ≤ min v C + 1

lemma codeOf_zero : codeOf P I (fun _ => 0) = 0 := by
  simp [codeOf, Radix.enc]

lemma tab_init (C : ℕ) :
    Tab (I := I) (P := P) C [] 0 (fun c => if c = 0 then 1 else 0) where
  cap := fun c => by split <;> omega
  out := fun c hc => by
    have h1 : 0 < (P + 1) ^ I.machines := Nat.pow_pos (by omega)
    rw [if_neg (by omega)]
  ge := fun u v h => by
    obtain ⟨u0, hR, rfl⟩ := h
    cases hR
    rw [Nat.zero_sub, adv_zero (fun i => by omega), codeOf_zero, if_pos rfl]
    omega
  le := fun u hu hne => by
    have hc : codeOf P I u = 0 := by
      by_contra hcc
      exact hne (if_neg hcc)
    have hu0 : u = fun _ => 0 := by
      rw [← stOf_codeOf hu, hc]
      funext i
      simp [stOf, Radix.dig]
    refine ⟨0, ⟨fun _ => 0, ?_, ?_⟩, ?_⟩
    · exact Reach.nil 0 _
    · rw [hu0, Nat.zero_sub, adv_zero (fun i => by omega)]
    · rw [hc, if_pos rfl]; omega

lemma codeOf_inj {u u' : St I} (hu : ∀ i, u i ≤ P) (hu' : ∀ i, u' i ≤ P)
    (h : codeOf P I u = codeOf P I u') : u = u' := by
  rw [← stOf_codeOf hu, ← stOf_codeOf hu', h]

/-- **Letting time run.** -/
lemma tab_shift {C : ℕ} {L : List (Fin I.jobs)} {t t' : ℕ} {T : ℕ → ℕ}
    (h : Tab (I := I) (P := P) C L t T) (hrt : refOf I 0 L ≤ t) (htt : t ≤ t') :
    Tab (I := I) (P := P) C L t' (pushed P I.machines (t' - t) T ((P + 1) ^ I.machines)) := by
  refine ⟨fun c => pushed_le _ _ _ _ _ _ _ (fun k _ => h.cap k), fun c hc => ?_,
    fun u v hR => ?_, fun u hu hne => ?_⟩
  · rcases pushed_cases P I.machines (t' - t) T ((P + 1) ^ I.machines) c with h0 | ⟨k, hk, he, -⟩
    · exact h0
    · exact absurd (he ▸ advOf_lt (le_refl ((P + 1) ^ I.machines)) (δ := t' - t) (c := k)) (by omega)
  · obtain ⟨u0, hReach, rfl⟩ := hR
    have hu0 : ∀ i, (adv P (t - refOf I 0 L) u0) i ≤ P := fun i => by simp [adv]
    have hmid : ReachAt I P L t (adv P (t - refOf I 0 L) u0) v := ⟨u0, hReach, rfl⟩
    have hcode : advOf P I.machines (t' - t) (codeOf P I (adv P (t - refOf I 0 L) u0))
        = codeOf P I (adv P (t' - refOf I 0 L) u0) := by
      rw [advOf_codeOf _ hu0, adv_adv]
      congr 2
      omega
    exact le_trans (h.ge _ v hmid)
      (pushed_ge (codeOf_lt hu0) hcode)
  · rcases pushed_cases P I.machines (t' - t) T ((P + 1) ^ I.machines) (codeOf P I u) with
      h0 | ⟨k, hk, he, heq⟩
    · exact absurd h0 hne
    · have hTk : T k ≠ 0 := by rw [← heq]; exact hne
      have hkc : codeOf P I (stOf P I k) = k := codeOf_stOf hk
      obtain ⟨v, hRv, hle⟩ := h.le (stOf P I k) (fun i => stOf_le k i) (by rw [hkc]; exact hTk)
      obtain ⟨u0, hReach, hst⟩ := hRv
      have hueq : u = adv P (t' - refOf I 0 L) u0 := by
        refine codeOf_inj hu (fun i => by simp [adv]) ?_
        rw [← he, ← hkc, hst, advOf_codeOf _ (fun i => by simp [adv]), adv_adv]
        congr 2
        omega
      refine ⟨v, ⟨u0, hReach, hueq⟩, ?_⟩
      rw [heq, hkc] at *
      exact hle

/-! ### Placing a job -/

lemma reachAt_snoc {L : List (Fin I.jobs)} {j : Fin I.jobs} {u : St I} {v : ℕ} :
    ReachAt I P (L ++ [j]) (I.d j) u v ↔
      (∃ u' v', ReachAt I P L (I.d j) u' v' ∧ u = u' ∧ v = v') ∨
      (∃ u' v' i, ReachAt I P L (I.d j) u' v' ∧ i ∈ I.eligible j ∧ I.p j ≤ u' i ∧
        u = Function.update u' i 0 ∧ v = v' + I.w j) := by
  constructor
  · rintro ⟨u0, hR, rfl⟩
    obtain ⟨u', v1, v2, hR1, hs, rfl⟩ := reach_snoc_iff.mp hR
    have hb : ∀ i, u0 i ≤ P := reach_bounded hR (fun _ => by omega)
    rw [refOf_snoc, Nat.sub_self, adv_zero hb]
    cases hs with
    | drop =>
        exact Or.inl ⟨_, v1, ⟨u', hR1, rfl⟩, rfl, by omega⟩
    | place i hi hfree =>
        exact Or.inr ⟨_, v1, i, ⟨u', hR1, rfl⟩, hi, hfree, rfl, by omega⟩
  · have hz : ∀ (w : St I), (∀ i, w i ≤ P) →
        w = adv P (I.d j - refOf I 0 (L ++ [j])) w := by
      intro w hw
      rw [refOf_snoc, Nat.sub_self, adv_zero hw]
    rintro (⟨u', v', ⟨u0, hR1, rfl⟩, rfl, rfl⟩ | ⟨u', v', i, ⟨u0, hR1, rfl⟩, hi, hfree, rfl, rfl⟩)
    · exact ⟨_, reach_snoc_iff.mpr ⟨u0, _, 0, hR1, Step1.drop, by omega⟩,
        hz _ (fun i => by simp [adv])⟩
    · refine ⟨_, reach_snoc_iff.mpr ⟨u0, _, I.w j, hR1, Step1.place i hi hfree, rfl⟩, ?_⟩
      refine hz _ fun k => ?_
      by_cases hk : k = i
      · subst hk; simp
      · rw [Function.update_of_ne hk]; simp [adv]

/-- The table after `L`, with the job `j` optionally placed on a machine of `E`. -/
def ReachPart (I : Instance) (P : ℕ) (L : List (Fin I.jobs)) (j : Fin I.jobs)
    (Q : Fin I.machines → Prop) (t : ℕ) (u : St I) (v : ℕ) : Prop :=
  ReachAt I P L t u v ∨
    ∃ u' v' i, Q i ∧ ReachAt I P L t u' v' ∧ I.p j ≤ u' i ∧
      u = Function.update u' i 0 ∧ v = v' + I.w j

/-- The table with the job in hand partly placed. -/
structure TabPart (C : ℕ) (L : List (Fin I.jobs)) (j : Fin I.jobs)
    (Q : Fin I.machines → Prop) (t : ℕ) (T : ℕ → ℕ) : Prop where
  cap : ∀ c, T c ≤ C + 1
  out : ∀ c, (P + 1) ^ I.machines ≤ c → T c = 0
  ge : ∀ u v, ReachPart I P L j Q t u v → min v C + 1 ≤ T (codeOf P I u)
  le : ∀ u, (∀ i, u i ≤ P) → T (codeOf P I u) ≠ 0 →
    ∃ v, ReachPart I P L j Q t u v ∧ T (codeOf P I u) ≤ min v C + 1

lemma tabPart_nil {C : ℕ} {L : List (Fin I.jobs)} {j : Fin I.jobs} {t : ℕ} {T : ℕ → ℕ}
    (h : Tab (I := I) (P := P) C L t T) :
    TabPart (I := I) (P := P) C L j (fun _ => False) t T where
  cap := h.cap
  out := h.out
  ge := fun u v hR => by
    rcases hR with hR | hR2
    · exact h.ge u v hR
    · obtain ⟨u', v2, i, hmem, hrest⟩ := hR2
      exact absurd hmem (by simp)
  le := fun u hu hne => by
    obtain ⟨v, hR, hle⟩ := h.le u hu hne
    exact ⟨v, Or.inl hR, hle⟩

lemma cap_add (v w C : ℕ) : min (min v C + 1 + w) (C + 1) = min (v + w) C + 1 := by omega

/-- **Placing the job in hand on one more machine.** -/
lemma tabPart_relax {C : ℕ} {L : List (Fin I.jobs)} {j : Fin I.jobs}
    {Q : Fin I.machines → Prop} {t : ℕ} {T T2 : ℕ → ℕ} {i : Fin I.machines}
    (hT : Tab (I := I) (P := P) C L t T) (hT2 : TabPart (I := I) (P := P) C L j Q t T2)
    (hi : i ∈ I.eligible j) :
    TabPart (I := I) (P := P) C L j (fun k => Q k ∨ k = i) t
      (relaxed P i.val (I.p j) (I.w j) (C + 1) T T2 ((P + 1) ^ I.machines)) := by
  refine ⟨fun c => relaxed_le _ _ _ _ _ _ _ _ _ _ hT2.cap (le_refl _), fun c hc => ?_,
    fun u v hR => ?_, fun u hu hne => ?_⟩
  · rcases relaxed_cases P i.val (I.p j) (I.w j) (C + 1) T T2 ((P + 1) ^ I.machines) c with
      h0 | ⟨k, hk, -, -, hz, -⟩
    · rw [h0]; exact hT2.out c hc
    · exact absurd hz (by have := zeroAt_le P i.val k; omega)
  · rcases hR with hRA | ⟨u', v', i', hmem, hRA', hfree, rfl, rfl⟩
    · exact le_trans (hT2.ge u v (Or.inl hRA)) (relaxed_ge_base _ _)
    · rcases hmem with hmem' | rfl
      · exact le_trans (hT2.ge _ _ (Or.inr ⟨u', v', i', hmem', hRA', hfree, rfl, rfl⟩))
          (relaxed_ge_base _ _)
      · have hb : ∀ k, u' k ≤ P := reachAt_le hRA'
        have hTc : min v' C + 1 ≤ T (codeOf P I u') := hT.ge u' v' hRA'
        have hdg : Radix.dig P (codeOf P I u') i'.val = u' i' := dig_codeOf hb i'
        have hzc : zeroAt P i'.val (codeOf P I u') = codeOf P I (Function.update u' i' 0) :=
          zeroAt_codeOf i' hb
        refine le_trans ?_ (relaxed_ge (g := T2) (codeOf_lt hb) (by omega)
          (by rw [hdg]; exact hfree) hzc)
        rw [← cap_add v' (I.w j) C]
        exact min_le_min (by omega) (le_refl _)
  · rcases relaxed_cases P i.val (I.p j) (I.w j) (C + 1) T T2 ((P + 1) ^ I.machines)
      (codeOf P I u) with h0 | ⟨k, hk, hTk, hdg, hz, heq⟩
    · rw [h0] at hne ⊢
      obtain ⟨v, hR, hle⟩ := hT2.le u hu hne
      exact ⟨v, hR.imp id (fun h => by
        obtain ⟨u', v', i', hmem, hrest⟩ := h
        exact ⟨u', v', i', Or.inl hmem, hrest⟩), hle⟩
    · have hkc : codeOf P I (stOf P I k) = k := codeOf_stOf hk
      obtain ⟨v', hRA, hle⟩ := hT.le (stOf P I k) (fun i => stOf_le k i) (by rw [hkc]; exact hTk)
      have hueq : u = Function.update (stOf P I k) i 0 := by
        refine codeOf_inj hu (fun l => ?_) ?_
        · by_cases hl : l = i
          · subst hl; simp
          · rw [Function.update_of_ne hl]; exact stOf_le k l
        · rw [← zeroAt_codeOf i (fun l => stOf_le k l), hkc, hz]
      refine ⟨v' + I.w j, Or.inr ⟨stOf P I k, v', i, Or.inr rfl, hRA, ?_, hueq, rfl⟩, ?_⟩
      · have : Radix.dig P k i.val = stOf P I k i := rfl
        omega
      · rw [heq, ← cap_add v' (I.w j) C]
        rw [hkc] at hle
        exact min_le_min (by omega) (le_refl _)

lemma tabPart_congr {C : ℕ} {L : List (Fin I.jobs)} {j : Fin I.jobs}
    {Q Q' : Fin I.machines → Prop} {t : ℕ} {T : ℕ → ℕ}
    (h : TabPart (I := I) (P := P) C L j Q t T) (hQ : ∀ i, Q i ↔ Q' i) :
    TabPart (I := I) (P := P) C L j Q' t T := by
  have hRP : ∀ u v, ReachPart I P L j Q' t u v ↔ ReachPart I P L j Q t u v := by
    intro u v
    unfold ReachPart
    constructor
    · rintro (h1 | ⟨u', v', i, hq, hrest⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨u', v', i, (hQ i).mpr hq, hrest⟩
    · rintro (h1 | ⟨u', v', i, hq, hrest⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨u', v', i, (hQ i).mp hq, hrest⟩
  exact ⟨h.cap, h.out, fun u v hR => h.ge u v ((hRP u v).mp hR),
    fun u hu hne => (h.le u hu hne).imp fun v hv => ⟨(hRP u v).mpr hv.1, hv.2⟩⟩

/-- The table after the job in hand has been tried on the machines of `E`, in order. -/
def foldRelax (P : ℕ) (I : Instance) (pj wj C : ℕ) (T : ℕ → ℕ) :
    List (Fin I.machines) → (ℕ → ℕ) → (ℕ → ℕ)
  | [], T2 => T2
  | i :: E, T2 =>
      foldRelax P I pj wj C T E (relaxed P i.val pj wj C T T2 ((P + 1) ^ I.machines))

lemma foldRelax_snoc (pj wj C : ℕ) (T : ℕ → ℕ) (E : List (Fin I.machines))
    (i : Fin I.machines) (T2 : ℕ → ℕ) :
    foldRelax P I pj wj C T (E ++ [i]) T2
      = relaxed P i.val pj wj C T (foldRelax P I pj wj C T E T2) ((P + 1) ^ I.machines) := by
  induction E generalizing T2 with
  | nil => rfl
  | cons a E ih => simp only [List.cons_append, foldRelax, ih]

lemma foldRelax_le (pj wj C K : ℕ) (T : ℕ → ℕ) (E : List (Fin I.machines)) (T2 : ℕ → ℕ)
    (h2 : ∀ c, T2 c ≤ K) (hC : C ≤ K) : ∀ c, foldRelax P I pj wj C T E T2 c ≤ K := by
  induction E generalizing T2 with
  | nil => exact h2
  | cons a E ih =>
      exact ih _ (fun c => relaxed_le _ _ _ _ _ _ _ _ _ _ h2 hC)

lemma tabPart_fold {C : ℕ} {L : List (Fin I.jobs)} {j : Fin I.jobs} {t : ℕ} {T : ℕ → ℕ}
    (hT : Tab (I := I) (P := P) C L t T) :
    ∀ (E : List (Fin I.machines)) (Q : Fin I.machines → Prop) (T2 : ℕ → ℕ),
      TabPart (I := I) (P := P) C L j Q t T2 → (∀ i ∈ E, i ∈ I.eligible j) →
      TabPart (I := I) (P := P) C L j (fun k => Q k ∨ k ∈ E) t
        (foldRelax P I (I.p j) (I.w j) (C + 1) T E T2) := by
  intro E
  induction E with
  | nil => intro Q T2 h _; exact tabPart_congr h fun i => by simp
  | cons i E ih =>
      intro Q T2 h hall
      have h1 := tabPart_relax hT h (hall i List.mem_cons_self)
      have h2 := ih (fun k => Q k ∨ k = i) _ h1 fun k hk => hall k (List.mem_cons_of_mem _ hk)
      exact tabPart_congr h2 fun k => by simp [or_assoc, or_comm, or_left_comm]

/-- **One job of the sweep**, on a table that already stands at its deadline. -/
lemma tab_job' {C : ℕ} {L : List (Fin I.jobs)} {j : Fin I.jobs} {T : ℕ → ℕ}
    (hsh : Tab (I := I) (P := P) C L (I.d j) T)
    (E : List (Fin I.machines)) (hE : ∀ i, i ∈ E ↔ i ∈ I.eligible j) :
    Tab (I := I) (P := P) C (L ++ [j]) (I.d j)
      (foldRelax P I (I.p j) (I.w j) (C + 1) T E T) := by
  have hpart := tabPart_fold hsh E (fun _ => False) _ (tabPart_nil hsh)
    (fun i hi => (hE i).mp hi)
  have hfin : TabPart (I := I) (P := P) C L j (fun k => k ∈ I.eligible j) (I.d j) _ :=
    tabPart_congr hpart fun k => by simp [hE k]
  refine ⟨hfin.cap, hfin.out, fun u v hR => hfin.ge u v ?_, fun u hu hne => ?_⟩
  · rcases reachAt_snoc.mp hR with ⟨u', v', hRA, rfl, rfl⟩ | ⟨u', v', i, hRA, hi, hfree, rfl, rfl⟩
    · exact Or.inl hRA
    · exact Or.inr ⟨u', v', i, hi, hRA, hfree, rfl, rfl⟩
  · obtain ⟨v, hR, hle⟩ := hfin.le u hu hne
    refine ⟨v, ?_, hle⟩
    rcases hR with hRA | ⟨u', v', i, hi, hRA, hfree, rfl, rfl⟩
    · exact reachAt_snoc.mpr (Or.inl ⟨u, v, hRA, rfl, rfl⟩)
    · exact reachAt_snoc.mpr (Or.inr ⟨u', v', i, hRA, hi, hfree, rfl, rfl⟩)

/-! ### Reading the answer off the table -/

open Lax470956.Preprocessing in
/-- **The best entry of the table is the block's optimum**, capped. -/
lemma tab_best {C : ℕ} {L : List (Fin I.jobs)} {t : ℕ} {T : ℕ → ℕ} (hPj : ∀ j, I.p j ≤ P)
    (hT : Tab (I := I) (P := P) C L t T) (hord : Ord I L) (hnd : L.Nodup) {bst : ℕ}
    (hub : ∀ c, c < (P + 1) ^ I.machines → T c ≤ bst)
    (hat : bst = 0 ∨ ∃ c, c < (P + 1) ^ I.machines ∧ T c = bst) :
    bst = min (optimumOn I L.toFinset) C + 1 := by
  obtain ⟨u0, hR⟩ := exists_reach (I := I) (P := P) hPj hord hnd
  have hRA : ReachAt I P L t (adv P (t - refOf I 0 L) u0) (optimumOn I L.toFinset) :=
    ⟨u0, hR, rfl⟩
  have hbu : ∀ i, (adv P (t - refOf I 0 L) u0) i ≤ P := fun i => by simp [adv]
  have hge : min (optimumOn I L.toFinset) C + 1 ≤ T (codeOf P I _) := hT.ge _ _ hRA
  have hle : bst ≤ min (optimumOn I L.toFinset) C + 1 := by
    rcases hat with h0 | ⟨c, hc, hTc⟩
    · omega
    · by_cases hz : T c = 0
      · omega
      · have hcc : codeOf P I (stOf P I c) = c := codeOf_stOf hc
        obtain ⟨v, hRv, hlev⟩ := hT.le (stOf P I c) (fun i => stOf_le c i) (by rw [hcc]; exact hz)
        obtain ⟨u1, hR1, -⟩ := hRv
        have : v ≤ optimumOn I L.toFinset := reach_le (I := I) (P := P) hPj hord hnd hR1
        rw [hcc] at hlev
        omega
  have := hub _ (codeOf_lt hbu)
  omega

end Lax470956Proofs.SweepDP
