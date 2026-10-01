import Lax888481Proofs.ParseScan

/-!
The parser's second pass: for each literal, the first occurrence of its variable, the
number of earlier occurrences, and whether there are at most four in all. Quadratic, which is
polynomial.
-/

namespace Lax888481Proofs.ParseNames

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax888481Proofs.ParseSem Lax888481Proofs.ParseScan

variable {B : ℕ} {vs : List ℕ}

lemma idxOf_le_of_getD : ∀ (l : List ℕ) (i : ℕ) (v : ℕ), i < l.length → l.getD i 0 = v →
    l.idxOf v ≤ i
  | [], i, v, h, _ => by simp at h
  | a :: t, 0, v, _, hv => by
      simp only [List.getD_cons_zero] at hv
      simp [List.idxOf_cons, hv]
  | a :: t, i + 1, v, h, hv => by
      rw [List.idxOf_cons]
      by_cases ha : a = v
      · simp [ha]
      · have := idxOf_le_of_getD t i v (by simpa using h) (by simpa using hv)
        have hne : (a == v) = false := by simpa using ha
        simp only [hne, cond_false]; omega

/-- The first time a variable is seen is where it first occurs. -/
lemma idxOf_eq_of_fresh {i : ℕ} (hi : i < vs.length) (hc : (vs.take i).count (vs.getD i 0) = 0) :
    vs.idxOf (vs.getD i 0) = i := by
  have hle := idxOf_le_of_getD vs i _ hi rfl
  by_contra hne
  have hlt : vs.idxOf (vs.getD i 0) < i := by omega
  have hmem : vs.getD i 0 ∈ vs.take i := by
    have h1 := getD_idxOf (vs := vs) (getD_mem hi)
    rw [List.mem_iff_getElem]
    refine ⟨vs.idxOf (vs.getD i 0), by rw [List.length_take]; omega, ?_⟩
    rw [List.getElem_take]
    rw [List.getD_eq_getElem _ _ (by omega)] at h1
    exact h1
  have := List.count_pos_iff.mpr hmem
  omega

/-- What the pass knows of the first: the variables, in `vr`. -/
def NCtx (vs : List ℕ) (M : ℕ) (σ : Env) : Prop :=
  σ.vars "k" = vs.length ∧ (σ.arrs "vr").length = M ∧
    ∀ i < vs.length, (σ.arrs "vr").getD i 0 = vs.getD i 0

def innerBody : Com :=
  .seq (.ite (.eq (.get "vr" (V "i")) (V "v"))
      (.seq (.ite (.eq (V "cnt") (.lit 0)) (.assign "fo" (V "i")) .skip)
        (.seq (.ite (.lt (V "i") (V "q")) (bump "app") .skip) (bump "cnt")))
      .skip)
    (bump "i")

def innerLoop : Com := .seq (set "i" 0) (.while (.lt (V "i") (V "k")) innerBody)

def IInv (vs : List ℕ) (M q : ℕ) (σ : Env) : Prop :=
  NCtx vs M σ ∧ σ.vars "q" = q ∧ σ.vars "v" = vs.getD q 0 ∧ σ.vars "i" ≤ vs.length ∧
    σ.vars "cnt" = (vs.take (σ.vars "i")).count (vs.getD q 0) ∧
    σ.vars "app" = (vs.take (min (σ.vars "i") q)).count (vs.getD q 0) ∧
    σ.vars "fo" = if σ.vars "cnt" = 0 then 0 else vs.idxOf (vs.getD q 0)

theorem innerBody_spec (M q : ℕ) (hM : vs.length < M) (hB : M + 9 < B)
    (hvB : ∀ v ∈ vs, v < B) (hq : q < vs.length) :
    Spec B (fun σ => IInv vs M q σ ∧ σ.vars "i" < vs.length) innerBody
      (fun σ σ' => IInv vs M q σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  run_vcg
  all_goals obtain ⟨⟨hk, hlen, hvr⟩, hqv, hv, hile, hcnt, happ, hfo⟩ := ‹IInv vs M q σ›
  all_goals have hilt := ‹σ.vars "i" < vs.length›
  all_goals have hcs := count_take_succ (vs := vs) hilt (vs.getD q 0)
  all_goals have hcle : (vs.take (σ.vars "i")).count (vs.getD q 0) ≤ vs.length :=
    (le_trans List.count_le_length (by rw [List.length_take]; omega))
  all_goals have hale : (vs.take (min (σ.vars "i") q)).count (vs.getD q 0) ≤ vs.length :=
    (le_trans List.count_le_length (by rw [List.length_take]; omega))
  all_goals have hvi := hvr _ hilt
  all_goals have hviB : vs.getD (σ.vars "i") 0 < B := hvB _ (getD_mem hilt)
  all_goals have hvqB : vs.getD q 0 < B := hvB _ (getD_mem hq)
  all_goals try omega
  all_goals try (rw [hvi]; exact hviB)
  all_goals try (simp only [Env.setVar]; simp; omega)
  all_goals have hmin : (σ.vars "i" < q ∧ min (σ.vars "i" + 1) q = σ.vars "i" + 1 ∧ min (σ.vars "i") q = σ.vars "i") ∨ (¬ σ.vars "i" < q ∧ min (σ.vars "i" + 1) q = q ∧ min (σ.vars "i") q = q) := (by omega)
  all_goals simp only [IInv, NCtx, Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals have hif : (if vs.getD (σ.vars "i") 0 = vs.getD q 0 then 1 else 0) = (if (σ.arrs "vr").getD (σ.vars "i") 0 = σ.vars "v" then 1 else 0) := (by rw [hvi, hv])
  all_goals rw [hif] at hcs
  all_goals first
    | rw [if_pos ‹_›] at hcs
    | rw [if_neg ‹_›] at hcs
  all_goals refine ⟨⟨⟨hk, hlen, hvr⟩, hqv, hv, by omega, ?_, ?_, ?_⟩, trivial⟩
  all_goals first
    | omega
    | (rcases hmin with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h2] <;> rw [h3] at happ <;> omega)
    | exact hfo
    | (rw [if_neg (by omega)]; rw [if_neg ‹_›] at hfo; exact hfo)
    | (rw [if_neg (by omega)]
       have hmt : vs.getD (σ.vars "i") 0 = vs.getD q 0 := (by rw [← hvi, ← hv]; assumption)
       have hfr := idxOf_eq_of_fresh hilt (by rw [hmt, ← hcnt]; assumption)
       rw [hmt] at hfr
       exact hfr.symm)

theorem innerLoop_ghost (M q : ℕ) (hM : vs.length < M) (hB : M + 9 < B)
    (hvB : ∀ v ∈ vs, v < B) (hq : q < vs.length) :
    Spec B (fun σ => IInv vs M q (σ.setVar "i" 0)) innerLoop
      (fun _ σ' => IInv vs M q σ' ∧ σ'.vars "i" = vs.length) ((40 + 4) * vs.length + 6) :=
  Spec.forRangeZero "i" "k" (IInv vs M q) vs.length 40 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.1.1) (innerBody_spec M q hM hB hvB hq)

/-- **One literal**: how often its variable occurs, how often before it, and where first. -/
theorem innerLoop_spec (M : ℕ) (hM : vs.length < M) (hB : M + 9 < B) (hvB : ∀ v ∈ vs, v < B) :
    Spec B (fun σ => NCtx vs M σ ∧ σ.vars "q" < vs.length ∧ σ.vars "v" = vs.getD (σ.vars "q") 0 ∧
        σ.vars "cnt" = 0 ∧ σ.vars "app" = 0 ∧ σ.vars "fo" = 0) innerLoop
      (fun σ σ' => NCtx vs M σ' ∧ σ'.vars "cnt" = vs.count (vs.getD (σ.vars "q") 0) ∧
        σ'.vars "app" = appOf vs (σ.vars "q") ∧ σ'.vars "fo" = nameOf vs (σ.vars "q"))
      (44 * vs.length + 6) := by
  intro σ ⟨hctx, hq, hv, hc, ha, hf⟩
  obtain ⟨σ', hrun, hI, hi⟩ := innerLoop_ghost M (σ.vars "q") hM hB hvB hq σ
    ⟨by simpa [NCtx, Env.setVar] using hctx, by simp [Env.setVar], by simpa [Env.setVar] using hv,
      by simp [Env.setVar], by simp [Env.setVar, hc], by simp [Env.setVar, ha],
      by simp [Env.setVar, hc, hf]⟩
  obtain ⟨hctx', -, -, -, hcnt, happ, hfo⟩ := hI
  rw [hi, List.take_length] at hcnt
  rw [hi, Nat.min_eq_right (by omega)] at happ
  have hpos : 0 < vs.count (vs.getD (σ.vars "q") 0) := List.count_pos_iff.mpr (getD_mem hq)
  rw [if_neg (by omega)] at hfo
  exact ⟨σ', hrun, hctx', hcnt, happ, hfo⟩

lemma wvars_innerLoop : innerLoop.wvars = ["i", "fo", "app", "cnt", "i"] := by
  simp [innerLoop, innerBody, Com.wvars]

lemma warrs_innerLoop : innerLoop.warrs = [] := by
  simp [innerLoop, innerBody, Com.warrs]

lemma noWrite_innerLoop : innerLoop.NoWrite := by
  simp [innerLoop, innerBody, Com.NoWrite]

lemma getD_set_fn (arr : List ℕ) (q : ℕ) (f : ℕ → ℕ) (hq : q < arr.length)
    (h : ∀ j < q, arr.getD j 0 = f j) : ∀ j < q + 1, (arr.set q (f q)).getD j 0 = f j := by
  intro j hj
  rcases Nat.lt_or_ge j q with hlt | hge
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
    exact h j hlt
  · have : j = q := by omega
    subst this
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hq]; rfl

lemma appOf_le (vs : List ℕ) (q : ℕ) : appOf vs q ≤ vs.length :=
  le_trans List.count_le_length (by rw [List.length_take]; omega)

def outerInit : Com :=
  .seq (.assign "v" (.get "vr" (V "q"))) (.seq (set "cnt" 0) (.seq (set "app" 0) (set "fo" 0)))

def outerFin : Com :=
  .seq (.store "nm" (V "q") (V "fo")) (.seq (.store "ap" (V "q") (V "app"))
    (.seq (.ite (.lt (V "cnt") (.lit 5)) .skip (set "ok" 0)) (bump "q")))

def outerBody : Com := .seq outerInit (.seq innerLoop outerFin)

def outerLoop : Com := .seq (set "q" 0) (.while (.lt (V "q") (V "k")) outerBody)

def OInv (vs : List ℕ) (M : ℕ) (σ : Env) : Prop :=
  NCtx vs M σ ∧ σ.vars "q" ≤ vs.length ∧ (σ.arrs "nm").length = M ∧ (σ.arrs "ap").length = M ∧
    (∀ j < σ.vars "q", (σ.arrs "nm").getD j 0 = nameOf vs j ∧ (σ.arrs "ap").getD j 0 = appOf vs j) ∧
    σ.vars "ok" ≤ 1 ∧ (σ.vars "ok" = 1 ↔ ∀ j < σ.vars "q", vs.count (vs.getD j 0) ≤ 4)

theorem outerBody_spec (M K : ℕ) (hM : vs.length < M) (hB : M + 9 < B) (hvB : ∀ v ∈ vs, v < B)
    (hK : 44 * vs.length + 6 = K) :
    Spec B (fun σ => OInv vs M σ ∧ σ.vars "q" < vs.length) outerBody
      (fun σ σ' => OInv vs M σ' ∧ σ'.vars "q" = σ.vars "q" + 1) (K + 40) := by
  have hnw := noWrite_innerLoop
  have hin : Spec B _ innerLoop _ K := hK ▸ (innerLoop_spec (B := B) M hM hB hvB)
  run_vcg [hin.frame]
  all_goals obtain ⟨⟨hk, hlen, hvr⟩, hqle, hl1, hl2, hcell, hok1, hok⟩ := ‹OInv vs M σ›
  all_goals have hqlt := ‹σ.vars "q" < vs.length›
  all_goals have hvq := hvr _ hqlt
  all_goals have hvqB : vs.getD (σ.vars "q") 0 < B := hvB _ (getD_mem hqlt)
  all_goals have hnl := nameOf_lt (vs := vs) hqlt
  all_goals have hal := appOf_le vs (σ.vars "q")
  all_goals have hcl : vs.count (vs.getD (σ.vars "q") 0) ≤ vs.length := List.count_le_length
  all_goals try
    (obtain ⟨⟨hctx', hcnt', happ', hfo'⟩, hfv, hfa, -, -⟩ := ‹(NCtx vs M _ ∧ _) ∧ _›
     have hq' := hfv "q" (by simp [wvars_innerLoop])
     have hok' := hfv "ok" (by simp [wvars_innerLoop])
     have hnm' := hfa "nm" (by simp [warrs_innerLoop])
     have hap' := hfa "ap" (by simp [warrs_innerLoop]))
  all_goals try simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte] at *
  all_goals try omega
  all_goals try (rw [hvq]; exact hvqB)
  · obtain ⟨hk', hlen', hvr'⟩ := hctx'
    simp only [OInv, NCtx, String.reduceEq, ↓reduceIte]
    rw [hq', hfo', happ', hnm', hap']
    have hcell' : ∀ j < σ.vars "q" + 1,
        ((σ.arrs "nm").set (σ.vars "q") (nameOf vs (σ.vars "q"))).getD j 0 = nameOf vs j ∧
        ((σ.arrs "ap").set (σ.vars "q") (appOf vs (σ.vars "q"))).getD j 0 = appOf vs j :=
      fun j hj => ⟨getD_set_fn _ _ (nameOf vs) (by omega) (fun j hj => (hcell j hj).1) j hj,
        getD_set_fn _ _ (appOf vs) (by omega) (fun j hj => (hcell j hj).2) j hj⟩
    refine ⟨⟨⟨hk', hlen', hvr'⟩, by omega, by rw [List.length_set, hl1],
      by rw [List.length_set, hl2], hcell', ?_, ?_⟩, by omega⟩
    · omega
    · rw [Nat.forall_lt_succ_right, hok', hok, ← hcnt']
      exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
  · obtain ⟨hk', hlen', hvr'⟩ := hctx'
    simp only [OInv, NCtx, String.reduceEq, ↓reduceIte]
    rw [hq', hfo', happ', hnm', hap']
    have hcell' : ∀ j < σ.vars "q" + 1,
        ((σ.arrs "nm").set (σ.vars "q") (nameOf vs (σ.vars "q"))).getD j 0 = nameOf vs j ∧
        ((σ.arrs "ap").set (σ.vars "q") (appOf vs (σ.vars "q"))).getD j 0 = appOf vs j :=
      fun j hj => ⟨getD_set_fn _ _ (nameOf vs) (by omega) (fun j hj => (hcell j hj).1) j hj,
        getD_set_fn _ _ (appOf vs) (by omega) (fun j hj => (hcell j hj).2) j hj⟩
    refine ⟨⟨⟨hk', hlen', hvr'⟩, by omega, by rw [List.length_set, hl1],
      by rw [List.length_set, hl2], hcell', ?_, ?_⟩, by omega⟩
    · omega
    · rw [Nat.forall_lt_succ_right, ← hcnt']
      exact ⟨fun h => by omega, fun h => absurd h.2 (by omega)⟩
  · exact ⟨⟨hk, hlen, hvr⟩, hqlt, hvq, trivial, trivial, trivial⟩
  · rw [hq', hnm', hl1]; omega
  · rw [hq', hap', hl2]; omega

theorem outerLoop_ghost (M K : ℕ) (hM : vs.length < M) (hB : M + 9 < B) (hvB : ∀ v ∈ vs, v < B)
    (hK : 44 * vs.length + 6 = K) :
    Spec B (fun σ => OInv vs M (σ.setVar "q" 0)) outerLoop
      (fun _ σ' => OInv vs M σ' ∧ σ'.vars "q" = vs.length) ((K + 40 + 4) * vs.length + 6) :=
  Spec.forRangeZero "q" "k" (OInv vs M) vs.length (K + 40) (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.1) (outerBody_spec M K hM hB hvB hK)

/-- What the second pass leaves behind. -/
def Named (vs : List ℕ) (M : ℕ) (σ : Env) : Prop :=
  NCtx vs M σ ∧ (σ.arrs "nm").length = M ∧ (σ.arrs "ap").length = M ∧
    (∀ j < vs.length, (σ.arrs "nm").getD j 0 = nameOf vs j ∧ (σ.arrs "ap").getD j 0 = appOf vs j) ∧
    σ.vars "ok" ≤ 1 ∧ (σ.vars "ok" = 1 ↔ ∀ v ∈ vs, vs.count v ≤ 4)

/-- **The second pass.** -/
theorem outerLoop_spec (M K : ℕ) (hM : vs.length < M) (hB : M + 9 < B) (hvB : ∀ v ∈ vs, v < B)
    (hK : 44 * vs.length + 6 = K) :
    Spec B (fun σ => NCtx vs M σ ∧ (σ.arrs "nm").length = M ∧ (σ.arrs "ap").length = M ∧
        σ.vars "ok" = 1) outerLoop
      (fun _ σ' => Named vs M σ') ((K + 40 + 4) * vs.length + 6) := by
  intro σ ⟨hctx, h1, h2, hok⟩
  obtain ⟨σ', hrun, hI, hq⟩ := outerLoop_ghost M K hM hB hvB hK σ
    ⟨by simpa [NCtx, Env.setVar] using hctx, by simp [Env.setVar], by simpa [Env.setVar] using h1,
      by simpa [Env.setVar] using h2, by simp [Env.setVar], by simp [Env.setVar, hok],
      by simp [Env.setVar, hok]⟩
  obtain ⟨hctx', -, hn1, hn2, hcell, hok1, hokiff⟩ := hI
  rw [hq] at hcell hokiff
  refine ⟨σ', hrun, hctx', hn1, hn2, hcell, hok1, hokiff.trans ⟨fun h v hv => ?_, fun h j hj => h _ (getD_mem hj)⟩⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
  have := h j hj
  rwa [List.getD_eq_getElem _ _ hj] at this

lemma wvars_outerLoop : outerLoop.wvars =
    ["q", "v", "cnt", "app", "fo", "i", "fo", "app", "cnt", "i", "ok", "q"] := by
  simp [outerLoop, outerBody, outerInit, outerFin, innerLoop, innerBody, Com.wvars]

lemma warrs_outerLoop : outerLoop.warrs = ["nm", "ap"] := by
  simp [outerLoop, outerBody, outerInit, outerFin, innerLoop, innerBody, Com.warrs]

lemma noWrite_outerLoop : outerLoop.NoWrite := by
  simp [outerLoop, outerBody, outerInit, outerFin, innerLoop, innerBody, Com.NoWrite]

end Lax888481Proofs.ParseNames
