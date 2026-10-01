import Lax888481Proofs.BruteEval

/-!
The odometer and the enumeration.
-/

namespace Lax888481Proofs.BruteRun

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax888481.Scheduling Lax888481.Scheduling.Instance
open Lax888481.InstanceEncoding
open Lax888481Proofs.SweepProg Lax888481Proofs.BruteProg Lax888481Proofs.SweepBody
open Lax888481Proofs.BruteEval

open scoped Classical

variable {B : ℕ} {x : List ℕ} {I : Instance} {W : ℕ}

/-- The arithmetic of one carry step. `a` is the old digit, `cy` the carry in; the sum
`a + cy` is at most `m + 1`, and the digit becomes the sum, or zero when the sum is
`m + 1` and the carry goes on. -/
lemma carry_arith (m i cy a ea ed : ℕ) (ha : a ≤ m) (hcy : cy ≤ 1)
    (IH : ea + cy * (m + 1) ^ i = ed + 1) :
    (a + cy ≤ m → ea + (a + cy) * (m + 1) ^ i + 0 * (m + 1) ^ (i + 1) = ed + a * (m + 1) ^ i + 1) ∧
    (¬ a + cy ≤ m → ea + 0 * (m + 1) ^ i + 1 * (m + 1) ^ (i + 1) = ed + a * (m + 1) ^ i + 1) := by
  constructor
  · intro h
    nlinarith [IH]
  · intro h
    have h1 : m + 1 = a + cy := by omega
    rw [pow_succ]
    generalize (m + 1) ^ i = P at IH ⊢
    rw [h1]
    nlinarith [IH]

/-- The state of the carry pass: the digits below `i` are the advanced ones, the rest are
the original `d0`, and the arithmetic says the advanced prefix plus the carry is the old prefix
plus one. -/
def OdoInv (I : Instance) (d0 : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = I.jobs ∧ σ.vars "m" = I.machines ∧ (σ.arrs "asg").length = I.jobs ∧
    σ.vars "cy" ≤ 1 ∧ σ.vars "i" ≤ I.jobs ∧
    (∀ j, σ.vars "i" ≤ j → (σ.arrs "asg").getD j 0 = d0 j) ∧
    (∀ j, (σ.arrs "asg").getD j 0 ≤ I.machines) ∧
    Radix.enc I.machines (σ.vars "i") (dgOf σ) + σ.vars "cy" * (I.machines + 1) ^ σ.vars "i" =
      Radix.enc I.machines (σ.vars "i") d0 + 1

lemma odo_step {d0 : ℕ → ℕ} (hd0 : ∀ j, d0 j ≤ I.machines) {σ σ' : Env}
    (h : OdoInv I d0 σ) (hi : σ.vars "i" < I.jobs) (v c : ℕ) (hc : c ≤ 1)
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m") (hci : σ'.vars "cy" = c)
    (hii : σ'.vars "i" = σ.vars "i" + 1)
    (hA : σ'.arrs "asg" = (σ.arrs "asg").set (σ.vars "i") v)
    (hcase : (v = d0 (σ.vars "i") + σ.vars "cy" ∧ c = 0 ∧ v ≤ I.machines) ∨
      (v = 0 ∧ c = 1 ∧ d0 (σ.vars "i") + σ.vars "cy" = I.machines + 1)) :
    OdoInv I d0 σ' := by
  obtain ⟨hn0, hm0, hlen, hcy, hile, hrest, hdig, hsum⟩ := h
  have hvm : v ≤ I.machines := by rcases hcase with ⟨-, -, h⟩ | ⟨h, -⟩ <;> omega
  have hlen' : (σ.arrs "asg").length = I.jobs := hlen
  have hdg' : ∀ j, j ≠ σ.vars "i" → dgOf σ' j = dgOf σ j := by
    intro j hj; simp only [dgOf, hA]; exact SweepTable.getD_set_other hj
  have hdgi : dgOf σ' (σ.vars "i") = v := by
    simp only [dgOf, hA]; exact SweepTable.getD_set_self (by omega)
  refine ⟨by rw [hn]; exact hn0, by rw [hm]; exact hm0, by rw [hA, List.length_set]; exact hlen,
    by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj
    rw [hii] at hj
    rw [hA, SweepTable.getD_set_other (by omega)]
    exact hrest j (by omega)
  · intro j
    by_cases hj : j = σ.vars "i"
    · subst hj; have := hdgi; simp only [dgOf] at this; omega
    · have := hdg' j hj; simp only [dgOf] at this; rw [this]; exact hdig j
  · rw [hii, hci, Radix.enc_succ, Radix.enc_succ (u := d0), hdgi]
    have hcg : Radix.enc I.machines (σ.vars "i") (dgOf σ') = Radix.enc I.machines (σ.vars "i") (dgOf σ) :=
      Radix.enc_congr fun j hj => hdg' j (by omega)
    rw [hcg]
    have := carry_arith I.machines (σ.vars "i") (σ.vars "cy") (d0 (σ.vars "i"))
      (Radix.enc I.machines (σ.vars "i") (dgOf σ)) (Radix.enc I.machines (σ.vars "i") d0)
      (hd0 _) hcy hsum
    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have := this.1 (by omega); rw [h1, h2]; linarith
    · have := this.2 (by omega); rw [h1, h2]; linarith

theorem carryBody_spec {d0 : ℕ → ℕ} (hd0 : ∀ j, d0 j ≤ I.machines) (hnB : I.jobs + 2 < B)
    (hmB : I.machines + 2 < B) :
    Spec B (fun σ => OdoInv I d0 σ ∧ σ.vars "i" < I.jobs) carryBody
      (fun σ σ' => OdoInv I d0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 60 := by
  run_vcg
  all_goals obtain ⟨hn, hm, hlen, hcy, hile, hrest, hdig, hsum⟩ := ‹OdoInv I d0 σ›
  all_goals have hi : σ.vars "i" < I.jobs := ‹σ.vars "i" < I.jobs›
  all_goals have hai : (σ.arrs "asg").getD (σ.vars "i") 0 = d0 (σ.vars "i") := hrest _ le_rfl
  all_goals have hdi := hd0 (σ.vars "i")
  all_goals try simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte, if_pos rfl] at *
  all_goals try omega
  · exact ⟨odo_step hd0 ‹OdoInv I d0 σ› hi 0 1 le_rfl (by simp) (by simp)
      (by show (σ.arrs "asg").getD (σ.vars "i") 0 + σ.vars "cy" - σ.vars "m" = 1; omega)
      (by simp) (by simp) (Or.inr ⟨rfl, rfl, by omega⟩), trivial⟩
  · exact ⟨odo_step hd0 ‹OdoInv I d0 σ› hi ((σ.arrs "asg").getD (σ.vars "i") 0 + σ.vars "cy")
      0 (by omega) (by simp) (by simp)
      (by show (σ.arrs "asg").getD (σ.vars "i") 0 + σ.vars "cy" - σ.vars "m" = 0; omega)
      (by simp) (by simp)
      (Or.inl ⟨by omega, rfl, by omega⟩), trivial⟩
/-- What the finished carry pass says about the number the digits read. -/
lemma odo_final {d0 : ℕ → ℕ} (hd0 : ∀ j, d0 j ≤ I.machines) {σ' : Env}
    (hO : OdoInv I d0 σ') (hi : σ'.vars "i" = I.jobs) :
    (σ'.vars "cy" = 1 ↔ Radix.enc I.machines I.jobs d0 + 1 = (I.machines + 1) ^ I.jobs) ∧
    Radix.enc I.machines I.jobs (dgOf σ') =
      (if σ'.vars "cy" = 1 then 0 else Radix.enc I.machines I.jobs d0 + 1) := by
  obtain ⟨-, -, -, hcy, -, -, hdig, hsum⟩ := hO
  rw [hi] at hsum
  have h1 : Radix.enc I.machines I.jobs d0 < (I.machines + 1) ^ I.jobs :=
    Radix.enc_lt (fun j _ => hd0 j)
  have h2 : Radix.enc I.machines I.jobs (dgOf σ') < (I.machines + 1) ^ I.jobs :=
    Radix.enc_lt (fun j _ => hdig j)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcy with h | h
  · rw [h] at hsum ⊢; simp at hsum ⊢; omega
  · rw [h] at hsum ⊢; simp at hsum ⊢; omega

theorem carryLoop_spec (hb : Bd B x I W) :
    Spec B (fun σ => σ.vars "n" = I.jobs ∧ σ.vars "m" = I.machines ∧
        (σ.arrs "asg").length = I.jobs ∧ ∀ j, (σ.arrs "asg").getD j 0 ≤ I.machines) carryLoop
      (fun σ σ' => OdoInv I (dgOf σ) σ' ∧ σ'.vars "i" = I.jobs ∧
        (∀ y, y ≠ "cy" → y ≠ "tt" → y ≠ "i" → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "asg" → σ'.arrs a = σ.arrs a)) ((60 + 4) * I.jobs + 6 + 2) := by
  intro σ ⟨hn, hm, hlen, hdig⟩
  have hnB := hb.nB
  have hmB := hb.mB
  have hd0 : ∀ j, dgOf σ j ≤ I.machines := hdig
  have hgen := Spec.forRangeZero (B := B) "i" "n" (OdoInv I (dgOf σ)) I.jobs 60
    (by omega) (fun σ h => h.2.2.2.2.1) (fun σ h => h.1)
    (Spec.mono (carryBody_spec hd0 hnB hmB) (le_refl _))
  obtain ⟨σ', hrun, hO, hi⟩ := hgen (σ.setVar "cy" 1)
    ⟨by simp [Env.setVar, hn], by simp [Env.setVar, hm], by simpa [Env.setVar] using hlen,
      by simp [Env.setVar], by simp [Env.setVar],
      fun j _ => by simp [Env.setVar, dgOf], fun j => by simpa [Env.setVar] using hdig j,
      by simp [Env.setVar]⟩
  have hr0 : Run B (set "cy" (lit 1)) σ (σ.setVar "cy" 1) 2 :=
    (Run.assign (v := 1) (SweepBody.evalB_lit (by omega))).mono (by norm_num [Expr.size])
  have hr : Run B carryLoop σ σ' ((60 + 4) * I.jobs + 6 + 2) :=
    (Run.seq hr0 hrun).mono (by omega)
  refine ⟨σ', hr, hO, hi, fun y h1 h2 h3 => ?_, fun a ha => ?_⟩
  · rw [hr.frame_var y (by simp [carryLoop, carryBody, Com.wvars]; tauto)]
  · rw [hr.frame_arr a (by simp [carryLoop, carryBody, Com.warrs]; exact ha)]

theorem recordStep_spec (hb : Bd B x I W) :
    Spec B (fun σ => Ctx x I W σ ∧ σ.vars "ans" ≤ 1 ∧ σ.vars "ok" ≤ 1 ∧ σ.vars "acc" ≤ W)
      recordStep
      (fun σ σ' => Only ["ans"] σ σ' ∧ σ'.vars "ans" ≤ 1 ∧
        (σ'.vars "ans" = 1 ↔ σ.vars "ans" = 1 ∨ (σ.vars "ok" = 1 ∧ σ.vars "acc" = W))) 20 := by
  run_vcg
  all_goals have hctx := ‹Ctx x I W σ›
  all_goals have hWv : σ.vars "W" = W := hctx.hW
  all_goals have hWB := hb.wB
  all_goals have hans : σ.vars "ans" ≤ 1 := ‹σ.vars "ans" ≤ 1›
  all_goals have hok : σ.vars "ok" ≤ 1 := ‹σ.vars "ok" ≤ 1›
  all_goals have hacc : σ.vars "acc" ≤ W := ‹σ.vars "acc" ≤ W›
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try omega
  · refine ⟨⟨fun y hy => ?_, fun a => rfl⟩, le_rfl, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      simp [hy]
    · simp only [true_iff]; right; exact ⟨‹σ.vars "ok" = 1›, by omega⟩
  all_goals refine ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, hans, ?_⟩
  all_goals constructor
  all_goals first
    | exact fun h => Or.inl h
    | (rintro (h | ⟨h1, h2⟩); exact h; exfalso; omega)

theorem dnStep_spec (hb : Bd B x I W) :
    Spec B (fun σ => σ.vars "cy" ≤ 1) dnStep
      (fun σ σ' => Only ["dn"] σ σ' ∧ σ'.vars "dn" = σ.vars "cy") 4 := by
  run_vcg
  all_goals have hcy : σ.vars "cy" ≤ 1 := ‹σ.vars "cy" ≤ 1›
  all_goals have := hb.nB
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try omega
  refine ⟨⟨fun y hy => ?_, fun a => rfl⟩, by simp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  simp [hy]

/-! ### The Enumeration -/

/-- A string is good when the schedule it reads is feasible and reaches the threshold. -/
def Good (I : Instance) (W t : ℕ) : Prop :=
  Feasible (Brute.schedOf I t) ∧ W ≤ weight (Brute.schedOf I t)

/-- The number the digits read. -/
def sOf (I : Instance) (σ : Env) : ℕ := Radix.enc I.machines I.jobs (dgOf σ)

/-- How many strings have been tried. -/
def cntOf (I : Instance) (σ : Env) : ℕ :=
  if σ.vars "dn" = 0 then sOf I σ else (I.machines + 1) ^ I.jobs

/-- How many strings are still to try. -/
def Vof (I : Instance) (σ : Env) : ℕ :=
  if σ.vars "dn" = 0 then (I.machines + 1) ^ I.jobs - sOf I σ else 0

/-- The state of the enumeration. -/
def BInv (x : List ℕ) (I : Instance) (W : ℕ) (σ : Env) : Prop :=
  Ctx x I W σ ∧ σ.vars "dn" ≤ 1 ∧ (σ.vars "dn" = 0 → sOf I σ < (I.machines + 1) ^ I.jobs) ∧
    σ.vars "ans" ≤ 1 ∧ (σ.vars "ans" = 1 ↔ ∃ t, t < cntOf I σ ∧ Good I W t)

lemma schedD_eq_schedOf {d : ℕ → ℕ} (hd : ∀ i, d i ≤ I.machines) :
    schedD I d = Brute.schedOf I (Radix.enc I.machines I.jobs d) := by
  funext j
  simp only [schedD, Brute.schedOf]
  rw [Radix.dig_enc (fun i _ => hd i) j.val j.isLt]

/-- The string just tested is good exactly when `ok` and `acc` say so. -/
lemma good_iff {d : ℕ → ℕ} (hd : ∀ i, d i ≤ I.machines) {ok acc : ℕ}
    (hok : ok = 1 ↔ Feasible (schedD I d))
    (hacc : acc = Brute.wacc I (schedD I d) W I.jobs) :
    (ok = 1 ∧ acc = W) ↔ Good I W (Radix.enc I.machines I.jobs d) := by
  rw [Good, ← schedD_eq_schedOf hd, hok, hacc, ← Brute.le_weight_iff]

/-- The cost of testing one string and moving on. -/
def Kbody (L n : ℕ) : ℕ :=
  (4 + ((44 * L + 128 + 4) * n + 6) + ((60 + (204 * n + 4) + 10 + 4) * n + 6)) + 20 +
    ((60 + 4) * n + 6 + 2) + 4

theorem bruteBody_spec (hb : Bd B x I W) :
    Spec B (fun σ => BInv x I W σ ∧ σ.vars "dn" = 0) bruteBody
      (fun σ σ' => BInv x I W σ' ∧ Vof I σ' < Vof I σ) (Kbody x.length I.jobs) := by
  intro σ ⟨hB, hdn0⟩
  obtain ⟨hctx, hdn1, hlt, hans1, hiffB⟩ := hB
  have hs : sOf I σ < (I.machines + 1) ^ I.jobs := hlt hdn0
  have hd0 : ∀ j, dgOf σ j ≤ I.machines := hctx.hdig
  obtain ⟨σ1, hr1, hc1, hasg1, hans1', hdn1', hok1, hokiff, haccEq⟩ := evalOne_spec hb σ hctx
  have hacc1 : σ1.vars "acc" ≤ W := by rw [haccEq, Brute.wacc_eq]; exact min_le_right _ _
  obtain ⟨σ2, hr2, hR, hans2, hansiff⟩ := recordStep_spec hb σ1
    ⟨hc1, by rw [hans1']; exact hans1, hok1, hacc1⟩
  have hc2 : Ctx x I W σ2 := hc1.only hR (by decide)
  have hasg2 : σ2.arrs "asg" = σ.arrs "asg" := by rw [hR.2, hasg1]
  have hdg2 : dgOf σ2 = dgOf σ := dgOf_congr hasg2
  obtain ⟨σ3, hr3, hO3, hi3, hfr3v, hfr3a⟩ :=
    carryLoop_spec hb σ2 ⟨hc2.hn, hc2.hm, hc2.hlen, hc2.hdig⟩
  rw [hdg2] at hO3
  have hfin := odo_final hd0 hO3 hi3
  obtain ⟨hn3, hm3, hlen3, hcy3, -, -, hdig3, -⟩ := hO3
  obtain ⟨σ4, hr4, hD, hdn4⟩ := dnStep_spec hb σ3 hcy3
  have hc3 : Ctx x I W σ3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hlen3, hdig3⟩
    · rw [hfr3a "a" (by decide)]; exact hc2.ha
    · exact hn3
    · exact hm3
    · rw [hfr3v "W" (by decide) (by decide) (by decide)]; exact hc2.hW
    · rw [hfr3v "O0" (by decide) (by decide) (by decide)]; exact hc2.hO0
    · rw [hfr3v "T0" (by decide) (by decide) (by decide)]; exact hc2.hT0
  have hc4 : Ctx x I W σ4 := hc3.only hD (by decide)
  have hdg4 : dgOf σ4 = dgOf σ3 := dgOf_congr (hD.2 "asg")
  have hans4 : σ4.vars "ans" = σ2.vars "ans" := by
    rw [hD.1 "ans" (by decide), hfr3v "ans" (by decide) (by decide) (by decide)]
  have hdn4' : σ4.vars "dn" = σ3.vars "cy" := hdn4
  have hs' : Radix.enc I.machines I.jobs (dgOf σ) = sOf I σ := rfl
  rw [hs'] at hfin
  have hgood := good_iff (W := W) hd0 hokiff haccEq
  rw [hs'] at hgood
  have hcnt : cntOf I σ4 = sOf I σ + 1 := by
    unfold cntOf sOf
    rw [hdn4', hdg4]
    by_cases h1 : σ3.vars "cy" = 1
    · rw [if_neg (by omega)]; have := hfin.1.mp h1; omega
    · rw [if_pos (by omega)]; rw [hfin.2, if_neg h1]; rfl
  refine ⟨σ4, (hr1.seq (hr2.seq (hr3.seq hr4))).mono (by unfold Kbody; omega), ⟨hc4, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hdn4']; exact hcy3
  · intro h0
    rw [hdn4'] at h0
    have h1 : ¬ σ3.vars "cy" = 1 := by omega
    unfold sOf
    rw [hdg4, hfin.2, if_neg h1]
    have : ¬ (sOf I σ + 1 = (I.machines + 1) ^ I.jobs) := fun h => h1 (hfin.1.mpr h)
    omega
  · rw [hans4]; exact hans2
  · rw [hans4, hcnt, hansiff, hans1', hiffB]
    unfold cntOf at *
    rw [if_pos hdn0]
    constructor
    · rintro (⟨t, ht, hg⟩ | h)
      · exact ⟨t, by omega, hg⟩
      · exact ⟨sOf I σ, by omega, (hgood.mp h)⟩
    · rintro ⟨t, ht, hg⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
      · exact Or.inl ⟨t, h, hg⟩
      · subst h; exact Or.inr (hgood.mpr hg)
  · unfold Vof
    rw [hdn4', if_pos hdn0]
    by_cases h1 : σ3.vars "cy" = 1
    · rw [if_neg (by omega)]; have := hfin.1.mp h1; omega
    · rw [if_pos (by omega)]
      unfold sOf; rw [hdg4, hfin.2, if_neg h1]
      have : ¬ (sOf I σ + 1 = (I.machines + 1) ^ I.jobs) := fun h => h1 (hfin.1.mpr h)
      unfold sOf at *; omega

theorem bruteLoop_spec (hb : Bd B x I W) :
    Spec B (fun σ => Ctx x I W σ ∧ ∀ j, (σ.arrs "asg").getD j 0 = 0) bruteLoop
      (fun _ σ' => BInv x I W σ' ∧ σ'.vars "dn" = 1)
      (4 + ((1 + 3 + Kbody x.length I.jobs) * (I.machines + 1) ^ I.jobs + 1 + 3)) := by
  intro σ ⟨hctx, hz⟩
  have hnB := hb.nB
  have hN : 0 < (I.machines + 1) ^ I.jobs := Nat.pow_pos (by omega)
  have hra : Run B (set "ans" (lit 0)) σ (σ.setVar "ans" 0) 2 :=
    (Run.assign (v := 0) (SweepBody.evalB_lit (by omega))).mono (by norm_num [Expr.size])
  have hrb : Run B (set "dn" (lit 0)) (σ.setVar "ans" 0) ((σ.setVar "ans" 0).setVar "dn" 0) 2 :=
    (Run.assign (v := 0) (SweepBody.evalB_lit (by omega))).mono (by norm_num [Expr.size])
  set σ0 := (σ.setVar "ans" 0).setVar "dn" 0 with hσ0
  have hOn : Only ["ans", "dn"] σ σ0 := by
    refine ⟨fun y hy => ?_, fun a => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2⟩ := hy
    simp [hσ0, Env.setVar, h1, h2]
  have hs0 : sOf I σ0 = 0 := by
    unfold sOf
    have : dgOf σ0 = fun _ => 0 := by
      funext j; exact hz j
    rw [this]; simp [Radix.enc]
  have hI0 : BInv x I W σ0 := by
    refine ⟨hctx.only hOn (by decide), by simp [hσ0, Env.setVar], ?_, by simp [hσ0, Env.setVar], ?_⟩
    · intro _; rw [hs0]; exact hN
    · have : cntOf I σ0 = 0 := by
        unfold cntOf; rw [if_pos (by simp [hσ0, Env.setVar]), hs0]
      rw [this]
      simp [hσ0, Env.setVar]
  have hwhile := Spec.while_count (B := B) (b := .eq (V "dn") (lit 0)) (c := bruteBody)
    (P := fun σ => BInv x I W σ) (K := (1 + 3 + Kbody x.length I.jobs) * (I.machines + 1) ^ I.jobs + 1 + 3)
    (BInv x I W) (Vof I) (Kbody x.length I.jobs)
    (fun σ h => ⟨_, SweepOrder.evalB_eqlit (by have := h.2.1; omega) (by omega)⟩)
    (fun σ ⟨h, hev⟩ => by
      have hdn : σ.vars "dn" = 0 := by
        rw [SweepOrder.evalB_eqlit (by have := h.2.1; omega) (by omega)] at hev
        simpa using hev
      exact bruteBody_spec hb σ ⟨h, hdn⟩)
    (fun σ h => h)
    (fun σ h => by
      have hV : Vof I σ ≤ (I.machines + 1) ^ I.jobs := by
        unfold Vof; split_ifs <;> omega
      have : (1 + (Cond.eq (V "dn") (lit 0)).size + Kbody x.length I.jobs) * Vof I σ ≤
          (1 + 3 + Kbody x.length I.jobs) * (I.machines + 1) ^ I.jobs :=
        Nat.mul_le_mul (by simp [Cond.size, Expr.size]) hV
      simp only [Cond.size, Expr.size] at this ⊢
      omega)
  obtain ⟨σ', hrun, hI', hfalse⟩ := hwhile σ0 hI0
  refine ⟨σ', (hra.seq (hrb.seq hrun)).mono (by omega), hI', ?_⟩
  rw [SweepOrder.evalB_eqlit (by have := hI'.2.1; omega) (by omega)] at hfalse
  have h1 := hI'.2.1
  simp at hfalse
  omega

theorem bruteWork_spec (hb : Bd B x I W) :
    Spec B (fun σ => Ctx x I W σ ∧ σ.out = [] ∧ ∀ j, (σ.arrs "asg").getD j 0 = 0) bruteWork
      (fun _ σ' => σ'.out = [if I.HasWeight W then 1 else 0])
      ((4 + ((1 + 3 + Kbody x.length I.jobs) * (I.machines + 1) ^ I.jobs + 1 + 3)) + 2) := by
  intro σ ⟨hctx, hout, hz⟩
  have hnB := hb.nB
  obtain ⟨σ1, hr1, ⟨hc1, hdn1, hlt, hans1, hiff⟩, hdn⟩ := bruteLoop_spec hb σ ⟨hctx, hz⟩
  have hout1 : σ1.out = [] := by
    rw [hr1.out_eq (by simp [bruteLoop, bruteBody, evalOne, jobsLoop, jobStep2, jobFetch,
      eligLoop, eligStep, jobFold, pairsLoop, pairOuterStep, pairFetch, pairInner, pairStep,
      recordStep, carryLoop, carryBody, dnStep, Com.NoWrite]), hout]
  have hev : (V "ans").evalB B σ1 = some (σ1.vars "ans") := SweepBody.evalB_var (by omega)
  refine ⟨_, (hr1.seq (Run.write hev)).mono (by simp [Expr.size]), ?_⟩
  simp only [hout1, List.nil_append]
  have hcnt : cntOf I σ1 = (I.machines + 1) ^ I.jobs := by
    unfold cntOf; rw [if_neg (by omega)]
  rw [hcnt] at hiff
  have hweight : I.HasWeight W ↔ σ1.vars "ans" = 1 := by
    rw [hiff, Brute.hasWeight_iff_exists]; rfl
  by_cases h : σ1.vars "ans" = 1
  · rw [if_pos (hweight.mpr h), h]
  · rw [if_neg (fun h' => h (hweight.mp h'))]
    have h0 : σ1.vars "ans" = 0 := by omega
    rw [h0]

end Lax888481Proofs.BruteRun
