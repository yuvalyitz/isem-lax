import Lax470956Proofs.FptProg

/-!
The capped power, and the two programs it chooses between.
-/

namespace Lax470956Proofs.FptRun

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.Scheduling Lax470956.Scheduling.Instance
open Lax470956.InstanceEncoding
open Lax470956Proofs.SweepProg Lax470956Proofs.BruteProg Lax470956Proofs.FptProg
open Lax470956Proofs.BruteEval
open Lax470956.SchedulingProblems

variable {B : ℕ} {x : List ℕ}

/-- One factor of the capped power. `f` is the capped power so far, `S` the true one. -/
lemma cap_step (P L f S : ℕ) (hf : f = min S (L + 1)) :
    (L / (P + 1) < f → L + 1 = min (S * (P + 1)) (L + 1)) ∧
    (¬ L / (P + 1) < f → f * (P + 1) = min (S * (P + 1)) (L + 1) ∧ f * (P + 1) ≤ L) := by
  have hdm := Nat.div_add_mod L (P + 1)
  have hml := Nat.mod_lt L (show 0 < P + 1 by omega)
  have hqL : L / (P + 1) ≤ L := Nat.div_le_self _ _
  set q := L / (P + 1) with hq
  set r := L % (P + 1) with hr
  constructor
  · intro h
    have hS : q + 1 ≤ S := by omega
    have : L + 1 ≤ S * (P + 1) := by nlinarith
    omega
  · intro h
    have hfq : f ≤ q := by omega
    have hfL : f * (P + 1) ≤ L := by nlinarith
    have hfS : f = S := by omega
    subst hfS
    exact ⟨by omega, hfL⟩

/-- The state of the capped power. -/
def CapInv (P L m : ℕ) (σ : Env) : Prop :=
  σ.vars "L" = L ∧ σ.vars "P" = P ∧ σ.vars "m" = m ∧ σ.vars "qq" = L / (P + 1) ∧
    σ.vars "i" ≤ m ∧ σ.vars "Sc" = min ((P + 1) ^ σ.vars "i") (L + 1)

theorem capBody_spec (P L m : ℕ) (hL : L + 2 < B) (hP : P + 2 < B) (hm : m + 2 < B) :
    Spec B (fun σ => CapInv P L m σ ∧ σ.vars "i" < m) capBody
      (fun σ σ' => CapInv P L m σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 30 := by
  run_vcg
  all_goals obtain ⟨hL', hP', hm', hqq, hile, hSc⟩ := ‹CapInv P L m σ›
  all_goals have hi : σ.vars "i" < m := ‹σ.vars "i" < m›
  all_goals have hcs := cap_step P L (σ.vars "Sc") ((P + 1) ^ σ.vars "i") hSc
  all_goals have hqL : L / (P + 1) ≤ L := Nat.div_le_self _ _
  all_goals have hSc1 : σ.vars "Sc" ≤ L + 1 := by rw [hSc]; exact min_le_right _ _
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try omega
  all_goals try (rw [hP']; have := (hcs.2 (by omega)).2; omega)
  · refine ⟨⟨hL', hP', hm', hqq, ?_, ?_⟩, trivial⟩
    · show σ.vars "i" + 1 ≤ m; omega
    · show σ.vars "L" + 1 = min ((P + 1) ^ (σ.vars "i" + 1)) (L + 1)
      rw [pow_succ, hL']; exact hcs.1 (by omega)
  · refine ⟨⟨hL', hP', hm', hqq, ?_, ?_⟩, trivial⟩
    · show σ.vars "i" + 1 ≤ m; omega
    · show σ.vars "Sc" * (σ.vars "P" + 1) = min ((P + 1) ^ (σ.vars "i" + 1)) (L + 1)
      rw [pow_succ, hP']; rw [hP'] at *; exact (hcs.2 (by omega)).1

theorem capInit_spec (P L : ℕ) (hL : L + 2 < B) (hP : P + 2 < B) :
    Spec B (fun σ => σ.vars "L" = L ∧ σ.vars "P" = P) capInit
      (fun σ σ' => σ'.vars "qq" = L / (P + 1) ∧ σ'.vars "Sc" = 1 ∧
        (∀ y, y ≠ "qq" → y ≠ "Sc" → σ'.vars y = σ.vars y) ∧ ∀ a, σ'.arrs a = σ.arrs a) 20 := by
  run_vcg
  all_goals have hL' : σ.vars "L" = L := ‹σ.vars "L" = L›
  all_goals have hP' : σ.vars "P" = P := ‹σ.vars "P" = P›
  all_goals have hqL : L / (P + 1) ≤ L := Nat.div_le_self _ _
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try omega
  · exact ⟨by rw [hL', hP'], trivial, fun y h1 h2 => by simp [h1, h2], fun a => trivial⟩
  · rw [hL', hP']; omega

theorem capLoop_spec (P L m : ℕ) (hL : L + 2 < B) (hP : P + 2 < B) (hm : m + 2 < B) :
    Spec B (fun σ => σ.vars "L" = L ∧ σ.vars "P" = P ∧ σ.vars "m" = m) capLoop
      (fun σ σ' => σ'.vars "L" = L ∧ σ'.vars "P" = P ∧ σ'.vars "m" = m ∧
        σ'.vars "Sc" = min ((P + 1) ^ m) (L + 1) ∧
        (∀ y, y ≠ "qq" → y ≠ "Sc" → y ≠ "i" → σ'.vars y = σ.vars y) ∧
        ∀ a, σ'.arrs a = σ.arrs a) (20 + ((30 + 4) * m + 6)) := by
  intro σ ⟨hL', hP', hm'⟩
  obtain ⟨σ1, hr1, hq1, hs1, hf1, ha1⟩ := capInit_spec P L hL hP σ ⟨hL', hP'⟩
  have hgen := Spec.forRangeZero (B := B) "i" "m" (CapInv P L m) m 30 (by omega)
    (fun σ h => h.2.2.2.2.1) (fun σ h => h.2.2.1) (capBody_spec P L m hL hP hm)
  obtain ⟨σ2, hr2, hI2, hi2⟩ := hgen σ1
    ⟨by rw [show (σ1.setVar "i" 0).vars "L" = σ1.vars "L" by simp [Env.setVar]]; rw [hf1 "L" (by decide) (by decide), hL'],
     by rw [show (σ1.setVar "i" 0).vars "P" = σ1.vars "P" by simp [Env.setVar]]; rw [hf1 "P" (by decide) (by decide), hP'],
     by rw [show (σ1.setVar "i" 0).vars "m" = σ1.vars "m" by simp [Env.setVar]]; rw [hf1 "m" (by decide) (by decide), hm'],
     by simp [Env.setVar, hq1],
     by simp [Env.setVar],
     by simp [Env.setVar, hs1]⟩
  have hr : Run B capLoop σ σ2 (20 + ((30 + 4) * m + 6)) := (Run.seq hr1 hr2).mono (by omega)
  obtain ⟨hL2, hP2, hm2, -, -, hSc2⟩ := hI2
  refine ⟨σ2, hr, hL2, hP2, hm2, by rw [hSc2, hi2], fun y h1 h2 h3 => ?_, fun a => ?_⟩
  · rw [hr.frame_var y (by simp [capLoop, capInit, capBody, Com.wvars]; tauto)]
  · exact hr.frame_arr a (by simp [capLoop, capInit, capBody, Com.warrs])

/-! ### Choosing -/

open Lax470956Proofs.SweepMain Lax470956Proofs.SweepPre Lax470956Proofs.SweepBody
open Lax470956.DynamicProgram (optimum)
open scoped Classical

/-- The cost of the brute force on a word of length `L` with `n` jobs and `m` machines. -/
def costB (L n m : ℕ) : ℕ :=
  (4 + ((1 + 3 + BruteRun.Kbody L n) * (m + 1) ^ n + 1 + 3)) + 2

/-- The cost of the sweep. -/
def costA (x : List ℕ) (m : ℕ) : ℕ :=
  1000 * ((pmaxOf x + 1) ^ m * ((m + 1) * (x.length + 1)))

/-- The cost of whichever of the two runs. -/
def Ksplit (x : List ℕ) (n m : ℕ) : ℕ :=
  if x.length < (pmaxOf x + 1) ^ m then costB x.length n m else costA x m

variable {Lo : ℕ}

set_option maxHeartbeats 2000000 in
theorem mainWork2_spec {I : Instance} {W : ℕ} (hdec : EncodesDecisionInstance x I W)
    (hB : 4 * (2 * mxE x + 2 * x.length + 1) + 64 ≤ B) (hlo : B ≤ Lo)
    (hmpos : 0 < I.machines) (hnpos : 0 < I.jobs) :
    Spec B (fun σ => Fresh I.jobs I.machines (min ((pmaxOf x + 1) ^ I.machines) (x.length + 1)) Lo σ ∧
        σ.arrs "a" = x ∧ σ.out = [] ∧ σ.vars "L" = x.length ∧
        σ.vars "n" = I.jobs ∧ σ.vars "m" = I.machines ∧ σ.vars "W" = W ∧ σ.vars "cap" = W ∧
        σ.vars "O0" = 2 + 3 * I.jobs ∧ σ.vars "T0" = 3 + 4 * I.jobs ∧
        (σ.arrs "asg").length = I.jobs ∧ ∀ j, (σ.arrs "asg").getD j 0 = 0)
      mainWork2 (fun _ σ' => σ'.out = [if W ≤ optimum I then 1 else 0])
      ((19 * I.jobs + 8) + (20 + ((30 + 4) * I.machines + 6)) +
        (1 + 3 + Ksplit x I.jobs I.machines)) := by
  classical
  obtain ⟨hEn, hxlen, hmc, hWv⟩ := enc_of_decision hdec
  have hmxB : mxE x + 2 < B := by omega
  have hxB : x.length + 2 < B := by omega
  have hxg : ∀ i, x.getD i 0 + 2 < B := fun i => by have := getD_le_mxE x i; omega
  have hnM : I.jobs ≤ mxE x := by rw [← hEn.jc]; exact getD_le_mxE x 0
  have hmM : I.machines ≤ mxE x := by rw [← hmc]; exact getD_le_mxE x 1
  have hpM : pmaxOf x ≤ mxE x := pmaxOf_le_mxE x
  have hnlex : 2 + I.jobs + I.jobs ≤ x.length := by omega
  intro σ ⟨hfr, hax, hout, hL, hn, hm, hW, hcap, hO0, hT0, hasgl, hasgz⟩
  obtain ⟨σ1, hr1, ⟨ha1, hn1, hP1, -⟩, hfv1, hfa1, -, ho1⟩ :=
    (pmaxLoop_spec (B := B) (x := x) (n := I.jobs) hxg (by omega) (by omega) (by omega)
      hEn.jc).frame σ ⟨hax, hn⟩
  have hv1 : ∀ y, y ≠ "P" → y ≠ "j" → y ≠ "v" → σ1.vars y = σ.vars y := fun y h1 h2 h3 =>
    hfv1 y (by simp [pmaxLoop, pmaxBody, Com.wvars]; tauto)
  have harr1 : ∀ a, σ1.arrs a = σ.arrs a := fun a =>
    hfa1 a (by simp [pmaxLoop, pmaxBody, Com.warrs])
  obtain ⟨σ2, hr2, hL2, hP2, hm2, hSc2, hv2, hfa2⟩ :=
    capLoop_spec (B := B) (pmaxOf x) x.length I.machines (by omega) (by omega) (by omega) σ1
      ⟨by rw [hv1 "L" (by decide) (by decide) (by decide)]; exact hL, hP1,
       by rw [hv1 "m" (by decide) (by decide) (by decide)]; exact hm⟩
  have hv12 : ∀ y, y ≠ "P" → y ≠ "j" → y ≠ "v" → y ≠ "qq" → y ≠ "Sc" → y ≠ "i" →
      σ2.vars y = σ.vars y := fun y h1 h2 h3 h4 h5 h6 => by
    rw [hv2 y h4 h5 h6, hv1 y h1 h2 h3]
  have harr2 : ∀ a, σ2.arrs a = σ.arrs a := fun a => by rw [hfa2, harr1]
  have hout2 : σ2.out = [] := by
    rw [hr2.out_eq (by simp [capLoop, capInit, capBody, Com.NoWrite]),
      hr1.out_eq (by simp [pmaxLoop, pmaxBody, Com.NoWrite])]
    exact hout
  have hLv : σ2.vars "L" = x.length := hL2
  have hScle : σ2.vars "Sc" ≤ x.length + 1 := by rw [hSc2]; exact min_le_right _ _
  have hcond : (Cond.lt (V "L") (V "Sc")).evalB B σ2 =
      some (decide (σ2.vars "L" < σ2.vars "Sc")) :=
    evalB_condLt (ReadHdr.evalB_var (by omega)) (ReadHdr.evalB_var (by omega))
  have hcty : Ctx x I W σ2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [harr2]; exact hax
    · rw [hv12 "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hn
    · rw [hv12 "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm
    · rw [hv12 "W" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hW
    · rw [hv12 "O0" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hO0
    · rw [hv12 "T0" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hT0
    · rw [harr2]; exact hasgl
    · intro j; rw [harr2, hasgz j]; omega
  by_cases hcase : x.length < (pmaxOf x + 1) ^ I.machines
  · have hSc : σ2.vars "Sc" = x.length + 1 := by rw [hSc2]; omega
    have hcT : (Cond.lt (V "L") (V "Sc")).evalB B σ2 = some true := by
      rw [hcond, hLv, hSc]; simp
    obtain ⟨σ3, hr3, hout3⟩ := BruteRun.bruteWork_spec (B := B) (x := x) (I := I) (W := W)
      ⟨hdec, by omega⟩ σ2 ⟨hcty, hout2, fun j => by rw [harr2]; exact hasgz j⟩
    refine ⟨σ3, (Run.seq hr1 (Run.seq hr2 (Run.ite_true (K := _) hcT hr3))).mono ?_, ?_⟩
    · simp only [Cond.size, Expr.size, Ksplit, if_pos hcase, costB]; omega
    · show σ3.out = _
      rw [hout3]
      have hh := hasWeight_iff I W
      by_cases h : W ≤ optimum I
      · rw [if_pos h, if_pos (hh.mpr h)]
      · rw [if_neg h, if_neg (fun h' => h (hh.mp h'))]
  · have hSc : σ2.vars "Sc" = (pmaxOf x + 1) ^ I.machines := by rw [hSc2]; omega
    have hcF : (Cond.lt (V "L") (V "Sc")).evalB B σ2 = some false := by
      rw [hcond, hLv, hSc]; simp; omega
    have hsz : Sizes B x I W Lo := ⟨hdec, hmpos, hnpos, by omega, hlo⟩
    have hfr' : Fresh I.jobs I.machines ((pmaxOf x + 1) ^ I.machines) Lo σ2 := by
      have hmin : min ((pmaxOf x + 1) ^ I.machines) (x.length + 1) = (pmaxOf x + 1) ^ I.machines := by
        omega
      rw [hmin] at hfr
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [harr2]
      exacts [hfr.lpw, hfr.locc, hfr.lfj, hfr.lst, hfr.lnx2, hfr.lnj, hfr.lord, hfr.ldl,
        hfr.lnc, hfr.lV, hfr.lV2, hfr.lVt, hfr.zocc, hfr.zfj]
    obtain ⟨σ3, hr3, hout3⟩ := mainWork_spec hsz σ2
      ⟨hfr', hcty.ha, hout2, hcty.hn, hcty.hm, hcty.hW,
        by rw [hv12 "cap" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcap,
        hcty.hO0, hcty.hT0⟩
    refine ⟨σ3, (Run.seq hr1 (Run.seq hr2 (Run.ite_false (K := _) hcF hr3))).mono ?_, hout3⟩
    simp only [Cond.size, Expr.size, Ksplit, if_neg hcase, costA]; omega

/-- The cost of the whole program, in IMP+ units. -/
def K2 (x : List ℕ) (n m : ℕ) : ℕ :=
  (24 * x.length + 62) + 25 + 20 + ((19 * n + 8) + (20 + ((30 + 4) * m + 6)) +
    (1 + 3 + Ksplit x n m))

set_option maxHeartbeats 2000000 in
theorem com2_spec {I : Instance} {W : ℕ} (hdec : EncodesDecisionInstance x I W)
    (hB : 4 * (2 * mxE x + 2 * x.length + 1) + 64 ≤ B) (hlo : B ≤ Lo) :
    Spec B (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "a").length = x.length ∧
        Fresh I.jobs I.machines (min ((pmaxOf x + 1) ^ I.machines) (x.length + 1)) Lo σ ∧
        (σ.arrs "asg").length = I.jobs ∧ ∀ j, (σ.arrs "asg").getD j 0 = 0)
      com2 (fun _ σ' => σ'.out = [if W ≤ optimum I then 1 else 0]) (K2 x I.jobs I.machines) := by
  classical
  obtain ⟨hEn, hxlen, hmc, hWv⟩ := enc_of_decision hdec
  have hmxB : mxE x + 2 < B := by omega
  have hxB : x.length + 2 < B := by omega
  have hy : ∀ v ∈ x, v < B := fun v hv => by
    have := Lax470956Proofs.Pmax.le_foldr_max hv; simp only [mxE] at hmxB; omega
  intro σ ⟨hinp, hout, halen, hfr, hasgl, hasgz⟩
  obtain ⟨σ1, hr1, ⟨ha1, hout1, hinp1, hL1, -⟩, hfv1, hfa1, -, -⟩ :=
    (ReadHdr.readWord_spec (B := B) (y := x) I.jobs (offset x I.jobs) hy (by omega) hEn.jc
      (by rw [offset, hEn.jc]; congr 1; omega) hxlen).frame σ ⟨hinp, hout, halen⟩
  have harr1 : ∀ a, a ≠ "a" → σ1.arrs a = σ.arrs a := fun a ha =>
    hfa1 a (by
      simp [ReadHdr.readWord, ReadHdr.readUpTo, Lax470956Proofs.ReadAll.readBody,
        Com.warrs]
      exact ha)
  obtain ⟨σ2, hr2, ⟨hn2, hm2, hW2, hcap2, hO02, hT02⟩, hfv2, hfa2, -, ho2⟩ :=
    (header_spec (B := B) (x := x) I.jobs I.machines W (fun i => by
        have := getD_le_mxE x i; omega) hxB (by omega)
      (by rw [← hEn.jc]; rfl) (by rw [← hmc]; rfl) hWv).frame σ1 ⟨ha1, hL1⟩
  have harr2 : ∀ a, σ2.arrs a = σ1.arrs a := fun a =>
    hfa2 a (by simp [header, Com.warrs])
  have ha2 : σ2.arrs "a" = x := by rw [harr2, ha1]
  have hout2 : σ2.out = [] := by rw [ho2 (by simp [header, Com.NoWrite]), hout1]
  have hL2 : σ2.vars "L" = x.length := by
    rw [hfv2 "L" (by simp [header, Com.wvars])]; exact hL1
  have harrσ : ∀ a, a ≠ "a" → σ2.arrs a = σ.arrs a := fun a ha => by rw [harr2, harr1 a ha]
  have hWlt : W < B := by have := getD_le_mxE x (x.length - 1); rw [hWv] at this; omega
  have hmM : I.machines ≤ mxE x := by rw [← hmc]; exact getD_le_mxE x 1
  have hnM : I.jobs ≤ mxE x := by rw [← hEn.jc]; exact getD_le_mxE x 0
  have hevW : (Cond.eq (V "W") (lit 0)).evalB B σ2 = some (σ2.vars "W" == 0) :=
    SweepOrder.evalB_eqlit (by rw [hW2]; omega) (by omega)
  have hevm : (Cond.eq (V "m") (lit 0)).evalB B σ2 = some (σ2.vars "m" == 0) :=
    SweepOrder.evalB_eqlit (by rw [hm2]; omega) (by omega)
  have hevn : (Cond.eq (V "n") (lit 0)).evalB B σ2 = some (σ2.vars "n" == 0) :=
    SweepOrder.evalB_eqlit (by rw [hn2]; omega) (by omega)
  have hdeg : optimum I = 0 → ∃ σ3, Run B degen σ2 σ3 6 ∧
      σ3.out = [if W ≤ optimum I then 1 else 0] := by
    intro hopt
    by_cases hW0 : W = 0
    · refine ⟨_, (Run.ite_true (K := 2) (by rw [hevW, hW2, hW0]; rfl)
        ((Run.write (ReadHdr.evalB_lit (show (1 : ℕ) < B by omega))).mono
          (by norm_num [Expr.size]))).mono (by norm_num [Cond.size, Expr.size]), ?_⟩
      simp only [hout2, hopt, if_pos (by omega : W ≤ 0)]
      rfl
    · refine ⟨_, (Run.ite_false (K := 2) (by
        rw [hevW, hW2]; simp [hW0])
        ((Run.write (ReadHdr.evalB_lit (show (0 : ℕ) < B by omega))).mono
          (by norm_num [Expr.size]))).mono (by norm_num [Cond.size, Expr.size]), ?_⟩
      simp only [hout2, hopt, if_neg (by omega : ¬ (W ≤ 0))]
      rfl
  by_cases hm0 : I.machines = 0
  · obtain ⟨σ3, hr3, hout3⟩ := hdeg (optimum_eq_zero_of_machines hm0)
    exact ⟨σ3, (Run.seq hr1 (Run.seq hr2 (Run.ite_true (K := 6)
      (by rw [hevm, hm2, hm0]; rfl) hr3))).mono (by
        simp only [Cond.size, Expr.size, K2]; omega), hout3⟩
  · by_cases hn0 : I.jobs = 0
    · obtain ⟨σ3, hr3, hout3⟩ := hdeg (optimum_eq_zero_of_jobs hn0)
      exact ⟨σ3, (Run.seq hr1 (Run.seq hr2 (Run.ite_false (K := 10)
        (by rw [hevm, hm2]; simp [hm0])
        (Run.ite_true (K := 6) (by rw [hevn, hn2, hn0]; rfl) hr3)))).mono (by
          simp only [Cond.size, Expr.size, K2]; omega), hout3⟩
    · have hfr2 : Fresh I.jobs I.machines (min ((pmaxOf x + 1) ^ I.machines) (x.length + 1)) Lo σ2 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          rw [harr2, harr1 _ (by decide)]
        exacts [hfr.lpw, hfr.locc, hfr.lfj, hfr.lst, hfr.lnx2, hfr.lnj, hfr.lord, hfr.ldl,
          hfr.lnc, hfr.lV, hfr.lV2, hfr.lVt, hfr.zocc, hfr.zfj]
      obtain ⟨σ3, hr3, hout3⟩ := mainWork2_spec (B := B) (Lo := Lo) hdec hB hlo (by omega)
        (by omega) σ2
        ⟨hfr2, ha2, hout2, hL2, hn2, hm2, hW2, hcap2, hO02, hT02,
          by rw [harrσ "asg" (by decide)]; exact hasgl,
          fun j => by rw [harrσ "asg" (by decide)]; exact hasgz j⟩
      refine ⟨σ3, (Run.seq hr1 (Run.seq hr2 (Run.ite_false (K := _)
        (by rw [hevm, hm2]; simp [hm0])
        (Run.ite_false (K := _) (by rw [hevn, hn2]; simp [hn0]) hr3)))).mono ?_, hout3⟩
      simp only [Cond.size, Expr.size, K2]
      omega

end Lax470956Proofs.FptRun
