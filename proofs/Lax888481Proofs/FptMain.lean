import Lax888481Proofs.FptRun

/-!
Theorem 3 as fixed-parameter tractability: the second program, run.
-/

namespace Lax888481Proofs.FptMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax888481.Scheduling Lax888481.Scheduling.Instance
open Lax888481.InstanceEncoding Lax888481.SchedulingProblems
open Lax888481.DynamicProgram (optimum)
open Lax888481.ParameterizedComplexity (Fits)
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax888481Proofs.SweepMain Lax888481Proofs.SweepBody Lax888481Proofs.FptProg
open Lax888481Proofs.FptRun

lemma rep_getD (n d : ℕ) : (List.replicate n (0 : ℕ)).getD d 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

/-- The value bound the program runs under. -/
def Bof2 (x : List ℕ) : ℕ := 4 * (2 * mxE x + 2 * x.length + 1) + 64

/-- The array lengths. -/
def extOf2 (x : List ℕ) : String → ℕ := fun a =>
  if a = "a" then x.length
  else if a = "pw" then machineCount x
  else if a = "occ" ∨ a = "fj" ∨ a = "st" ∨ a = "nx2" then Bof2 x
  else if a = "nj" ∨ a = "ord" ∨ a = "dl" ∨ a = "nc" ∨ a = "asg" then jobCount x
  else min ((pmaxOf x + 1) ^ machineCount x) (x.length + 1)

open Classical in
/-- The admissible words at word length `w`: the entries fit, and nothing else. -/
def Dom2 (w : ℕ) : Set (List ℕ) :=
  {x | x ∈ DecisionInstances ∧ Fits 12001 w x}

open Classical in
theorem solves2 (w : ℕ) :
    Solves layout2 com2 (Dom2 w)
      (fun x => if byMachinesAndPmax.Yes x then [1] else [0]) Bof2
      (fun x => K2 x (jobCount x) (machineCount x)) where
  ok := com2_ok
  inp := by
    intro x _ v hv
    have := Lax888481Proofs.Pmax.le_foldr_max hv
    simp only [Bof2, mxE] at *
    omega
  run := by
    intro x hx
    obtain ⟨I, W, hdec⟩ := hx.1
    obtain ⟨hEn, hxlen, hmc, hWv⟩ := enc_of_decision hdec
    have hfresh : Fresh I.jobs I.machines
        (min ((pmaxOf x + 1) ^ I.machines) (x.length + 1)) (Bof2 x)
        (initEnv (extOf2 x) x) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [initEnv, extOf2, List.length_replicate, hmc, hEn.jc] <;>
        first
          | rfl
          | (intro d; rw [List.getD_eq_getElem?_getD]
             rcases h : (List.replicate (Bof2 x) (0 : ℕ))[d]? with _ | v
             · rfl
             · have := List.getElem?_eq_some_iff.mp h
               obtain ⟨hd, hv⟩ := this
               rw [← hv, List.getElem_replicate])
          | simp
    have hasgz : ∀ j, ((initEnv (extOf2 x) x).arrs "asg").getD j 0 = 0 := fun d =>
      rep_getD _ d
    obtain ⟨σ', hrun, hout⟩ :=
      com2_spec (B := Bof2 x) (Lo := Bof2 x) hdec (by simp only [Bof2]; omega) (le_refl _)
        (initEnv (extOf2 x) x)
        ⟨rfl, rfl, by simp [initEnv, extOf2], hfresh, by simp [initEnv, extOf2, hEn.jc], hasgz⟩
    refine ⟨extOf2 x, σ', hrun.mono ?_, ?_⟩
    · rw [hEn.jc, hmc]
    · rw [hout]
      have hyes : byMachinesAndPmax.Yes x ↔ W ≤ optimum I := by
        constructor
        · rintro ⟨I', W', hdec', hw'⟩
          obtain ⟨rfl, rfl⟩ := decision_unique hdec' hdec
          exact (hasWeight_iff I' W').mp hw'
        · intro h
          exact ⟨I, W, hdec, (hasWeight_iff I W).mpr h⟩
      by_cases hc : W ≤ optimum I
      · rw [if_pos hc, if_pos (hyes.mpr hc)]
      · rw [if_neg hc, if_neg (fun h => hc (hyes.mp h))]

/-! ### The Function of the Parameter -/

/-- The size of the table, bounded by the parameter alone. -/
def Tof (k : ℕ) : ℕ := (k + 1) ^ k

/-- **The function of the parameter.** -/
def gFpt (k : ℕ) : ℕ := 4000 * ((k + 1) * (Tof k * (k + 1) ^ Tof k))

lemma Kbody_le (L n : ℕ) (h : n ≤ L) : BruteRun.Kbody L n ≤ 1000 * ((L + 1) * (L + 1)) := by
  unfold BruteRun.Kbody
  nlinarith [Nat.mul_le_mul h (le_refl L), Nat.mul_le_mul h h]

lemma K2_bound (x : List ℕ) (n : ℕ) (hn : n ≤ x.length) :
    K2 x n (machineCount x) ≤ gFpt (machineCount x + pmaxOf x) * (x.length + 1) := by
  set L := x.length with hL
  set m := machineCount x with hm
  set P := pmaxOf x with hP
  set k := m + P with hk
  have hT1 : 1 ≤ Tof k := Nat.one_le_pow _ _ (by omega)
  have hU1 : 1 ≤ (k + 1) ^ Tof k := Nat.one_le_pow _ _ (by omega)
  have hSle : (P + 1) ^ m ≤ Tof k :=
    le_trans (Nat.pow_le_pow_left (by omega : P + 1 ≤ k + 1) m)
      (Nat.pow_le_pow_right (by omega) (by omega : m ≤ k))
  set T := Tof k with hT
  set U := (k + 1) ^ T with hU
  have hA0 : 1 ≤ (L + 1) * ((k + 1) * (T * U)) := by
    have : 1 ≤ (k + 1) * (T * U) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hg : gFpt k * (L + 1) = 4000 * ((L + 1) * ((k + 1) * (T * U))) := by
    simp only [gFpt, hT, hU]; ring
  rw [hg]
  unfold K2 Ksplit costB costA
  by_cases hc : L < (P + 1) ^ m
  · rw [if_pos hc]
    have hLT : L + 1 ≤ T := by omega
    have hnT : n ≤ T := by omega
    have hQ : (m + 1) ^ n ≤ U :=
      le_trans (Nat.pow_le_pow_left (by omega : m + 1 ≤ k + 1) n)
        (Nat.pow_le_pow_right (by omega) hnT)
    have hKb := Kbody_le L n hn
    have h1 : (1 + 3 + BruteRun.Kbody L n) * (m + 1) ^ n ≤ (4 + 1000 * ((L + 1) * (L + 1))) * U :=
      Nat.mul_le_mul (by omega) hQ
    have h2 : (4 + 1000 * ((L + 1) * (L + 1))) * U ≤ 1004 * ((L + 1) * (T * U)) := by
      have this : (L + 1) * (L + 1) ≤ (L + 1) * T := Nat.mul_le_mul (le_refl _) hLT
      have e1 : (L + 1) * (L + 1) * U ≤ (L + 1) * T * U := Nat.mul_le_mul_right U this
      have e2 : U ≤ (L + 1) * (T * U) :=
        calc U = 1 * (1 * U) := by ring
          _ ≤ (L + 1) * (T * U) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul hT1 (le_refl _))
      nlinarith [e1, e2]
    have h3 : (L + 1) * (T * U) ≤ (L + 1) * ((k + 1) * (T * U)) :=
      Nat.mul_le_mul (le_refl _) (Nat.le_mul_of_pos_left _ (by omega))
    have h4 : (L + 1) * (k + 1) ≤ (L + 1) * ((k + 1) * (T * U)) :=
      Nat.mul_le_mul (le_refl _) (Nat.le_mul_of_pos_right _ (by positivity))
    nlinarith
  · rw [if_neg hc]
    have hS : (P + 1) ^ m * ((m + 1) * (L + 1)) ≤ T * ((k + 1) * (L + 1)) :=
      Nat.mul_le_mul hSle (Nat.mul_le_mul (by omega) (le_refl _))
    have h3 : T * ((k + 1) * (L + 1)) ≤ (L + 1) * ((k + 1) * (T * U)) := by
      have : T * ((k + 1) * (L + 1)) = (L + 1) * ((k + 1) * T) := by ring
      rw [this]
      exact Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) (Nat.le_mul_of_pos_right _ (by omega)))
    have h4 : (L + 1) * (k + 1) ≤ (L + 1) * ((k + 1) * (T * U)) :=
      Nat.mul_le_mul (le_refl _) (Nat.le_mul_of_pos_right _ (by positivity))
    nlinarith

def prog2 : Program := compileProgram layout2 com2

lemma gFpt_pos (k : ℕ) : 1 ≤ gFpt k := by
  unfold gFpt Tof
  have : 1 ≤ (k + 1) * ((k + 1) ^ k * (k + 1) ^ (k + 1) ^ k) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

set_option maxRecDepth 8000 in
open Classical in
theorem prog2_computesInTime (w : ℕ) :
    ComputesInTime w prog2 (Dom2 w)
      (fun x => if byMachinesAndPmax.Yes x then [1] else [0])
      (fun x => 12001 * gFpt (machineCount x + pmaxOf x) * (x.length + 1)) := by
  refine computesInTime_of_solves (solves2 w) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨⟨I, W, hdec⟩, hfits⟩ := hx
    have hne : x ≠ [] := by obtain ⟨y, rfl, -⟩ := hdec; simp
    have h1 := fits_max hne hfits
    refine fitsWords_of_max_le (by simp only [Bof2]; omega) ?_
    simp only [Layout.span, layout2, List.length_cons, List.length_nil, max_le_iff, Bof2]
    constructor <;> omega
  · obtain ⟨⟨I, W, hdec⟩, hfits⟩ := hx
    obtain ⟨hEn, hxlen, hmc, hWv⟩ := enc_of_decision hdec
    have hn : jobCount x ≤ x.length := by rw [hEn.jc]; omega
    have hb := K2_bound x (jobCount x) hn
    have hg := gFpt_pos (machineCount x + pmaxOf x)
    have hpos : 1 ≤ gFpt (machineCount x + pmaxOf x) * (x.length + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [const_eq2]
    have : 12001 * gFpt (machineCount x + pmaxOf x) * (x.length + 1)
        = 12001 * (gFpt (machineCount x + pmaxOf x) * (x.length + 1)) := by ring
    rw [this]
    omega

open Classical in
/-- **Theorem 3, as fixed-parameter tractability.** -/
theorem fpt : Lax888481.ParameterizedComplexity.FPT byMachinesAndPmax :=
  ⟨prog2, 12001, gFpt, fun w => prog2_computesInTime w⟩

end Lax888481Proofs.FptMain
