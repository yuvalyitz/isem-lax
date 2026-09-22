import Lax470956Proofs.PrintMain
import Lax470956Proofs.Checker

/-!
The printer runs in polynomial time on a word RAM.
-/

namespace Lax470956Proofs.PrintRam

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax470956Proofs.PrintModel Lax470956Proofs.EmitNat Lax470956Proofs.PrintProg
open Lax470956Proofs.PrintMain
open Lax470956Proofs.Checker (Shape shape_eq)
open Lax470956.InstanceEncoding

def layout : Layout :=
  ⟨["L", "rt", "rv", "J", "M", "T0", "O0", "R", "b", "j", "v", "u", "s", "i2", "i", "t", "f",
    "lo", "hi"], ["a"], 8⟩

theorem com_ok : Com.Ok layout com := by
  simp [com, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, guarded, work, headerNums,
    blocks, mLoop, row, iLoop, cell, scanLoop, scanBody, numLoop, numBody, emitNat, sizeLoop,
    sizeBody, onesLoop, onesBody, digLoop, digBody, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by simp [Layout.const]

def bnd (y : List ℕ) : ℕ := 16 * (y.length + y.foldr max 0) + 64

def Sz (y : List ℕ) : ℕ := (y.foldr max 0).size

lemma small (y : List ℕ) : Small (bnd y) (Sz y) y where
  entry := fun v hv => by
    have h := Lax470956Proofs.Pmax.le_foldr_max hv
    exact ⟨by simp only [bnd]; omega, Nat.size_le_size h⟩
  len := by simp only [bnd]; omega

def KW (y : List ℕ) : ℕ :=
  2 * (48 * Sz y + 40) + 3 * ((48 * Sz y + 60 + 4) * jobCount y + 6) +
    (((44 * room y + 6 + 30 + 4) * machineCount y + 6 + 30 + 4) * jobCount y + 6) + 50

open Classical in
noncomputable def Kc (y : List ℕ) : ℕ :=
  12 * y.length + (if Guard y then KW y else 0) + 100

theorem com_spec (y : List ℕ) :
    Spec (bnd y) (fun σ => σ.inp = y.length :: y ∧ σ.out = [] ∧ (σ.arrs "a").length = y.length)
      com (fun _ σ' => σ'.out = print y) (Kc y) := by
  have hs := small y
  have hB : ∀ v ∈ y, v < bnd y := fun v hv => by have := (hs.entry v hv).1; omega
  have hL' : y.length + 1 < bnd y := by have := hs.len; omega
  intro σ h
  obtain ⟨σ1, hrun1, hL, ha, hout, -⟩ := ReadAll.readAll_spec hB hL' σ h
  by_cases hg : Guard y
  · obtain ⟨σ2, hrun2, h2⟩ := guarded_spec hs (KW y) rfl σ1 ⟨ha, hL, hout⟩
    have hk : 12 * y.length + 10 + (KW y + 40) ≤ Kc y := by unfold Kc; rw [if_pos hg]; omega
    exact ⟨σ2, (Run.seq hrun1 hrun2).mono hk, h2⟩
  · obtain ⟨σ2, hrun2, h2⟩ := guarded_spec_no hs hg σ1 ⟨ha, hL, hout⟩
    have hk : 12 * y.length + 10 + 40 ≤ Kc y := by unfold Kc; rw [if_neg hg]; omega
    exact ⟨σ2, (Run.seq hrun1 hrun2).mono hk, h2⟩

/-! ### The machine program -/

theorem solves : Solves layout com Shape (fun y => print y.tail) (fun y => bnd y.tail)
    (fun y => Kc y.tail) where
  ok := com_ok
  inp := by
    intro y hy v hv
    have hs := small y.tail
    rw [shape_eq hy] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · have := hs.len; omega
    · have := (hs.entry v hv').1; omega
  run := by
    intro y hy
    obtain ⟨σ', hrun, hout⟩ := com_spec y.tail (initEnv (fun _ => y.tail.length) y)
      ⟨shape_eq hy, rfl, by simp [initEnv]⟩
    exact ⟨_, σ', hrun, hout⟩

def prog : Program := compileProgram layout com

theorem prog_computesInTime (w : ℕ) :
    ComputesInTime w prog
      {y | y ∈ Shape ∧ Lax470956.ParameterizedComplexity.Fits 100 w y}
      (fun y => print y.tail) (fun y => 10 * Kc y.tail + 1) := by
  have hs : Solves layout com
      {y | y ∈ Shape ∧ Lax470956.ParameterizedComplexity.Fits 100 w y} (fun y => print y.tail)
      (fun y => bnd y.tail) (fun y => Kc y.tail) :=
    ⟨solves.ok, fun y hy => solves.inp y hy.1, fun y hy => solves.run y hy.1⟩
  refine computesInTime_of_solves hs (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨hsh, hfits⟩ := hy
    have hne : y.headD 0 ∈ y := by
      rcases y with _ | ⟨a, t⟩
      · exact absurd rfl hsh.1
      · simpa using List.mem_cons_self
    have hylen : y.length = y.tail.length + 1 := by
      rcases y with _ | ⟨a, t⟩
      · exact absurd rfl hsh.1
      · simp
    have hbig : 100 * (y.length + y.tail.foldr max 0 + 1) ≤ 2 ^ w := by
      rcases Lax470956Proofs.Pmax.foldr_max_mem_or_zero y.tail with hm | hm
      · exact hfits _ (by rw [shape_eq hsh]; exact List.mem_cons_of_mem _ hm)
      · rw [hm]
        have := hfits _ hne
        omega
    refine fitsWords_of_max_le (by simp only [bnd]; omega) ?_
    simp only [Layout.span, layout, List.length_cons, List.length_nil, bnd, max_le_iff]
    omega
  · rw [const_eq]

/-! ### Polynomial time, in the bit-size currency -/

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding

lemma bitsNat_le_one {n v : ℕ} (hv : v ∈ bitsNat n) : v ≤ 1 := by
  simp only [bitsNat, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hv
  rcases hv with (⟨-, rfl⟩ | rfl) | ⟨i, -, rfl⟩
  · exact le_refl _
  · omega
  · unfold digit; omega

lemma print_le_one {y : List ℕ} {v : ℕ} (hv : v ∈ print y) : v ≤ 1 := by
  unfold print at hv
  split_ifs at hv
  · simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hv
    rcases hv with ((((h | h) | ⟨j, -, h⟩) | ⟨j, -, h⟩) | ⟨j, -, h⟩) | ⟨j, -, i, -, rfl⟩
    all_goals first
      | exact bitsNat_le_one h
      | (unfold eligBit; split_ifs <;> omega)
  · simp at hv

lemma Sz_le (x : List ℕ) : Sz x ≤ bitSize x + 1 := by
  unfold Sz
  rcases Lax470956Proofs.Pmax.foldr_max_mem_or_zero x with hm | hm
  · exact Nat.size_le.mpr (mem_lt_two_pow_bitSize_add_one hm)
  · rw [hm]; simp

lemma Kc_le (x : List ℕ) : 10 * Kc x + 1 ≤ 8221 * (bitSize x + 1) ^ 3 := by
  have hlen := length_le_bitSize x
  have hS := Sz_le x
  set N := bitSize x + 1 with hN
  have hN2 : N ≤ N * N := Nat.le_mul_self N
  have hN3 : N * N ≤ N * N * N := Nat.le_mul_of_pos_right _ (by omega)
  have hpow : N ^ 3 = N * N * N := by ring
  by_cases hg : Guard x
  · have hJ : jobCount x ≤ N := by have := hg.1; omega
    have hM : machineCount x ≤ N := by have := hg.2; omega
    have hR : room x ≤ N := by unfold room; omega
    have hKW : KW x ≤ 2 * (48 * N + 40) + 3 * ((48 * N + 60 + 4) * N + 6) +
        (((44 * N + 6 + 30 + 4) * N + 6 + 30 + 4) * N + 6) + 50 := by
      unfold KW; gcongr
    unfold Kc; rw [if_pos hg, hpow]
    nlinarith [hKW, hN2, hN3]
  · unfold Kc; rw [if_neg hg, hpow]
    nlinarith [hN2, hN3]

/-- **The printer is computable in polynomial time by a word RAM.** -/
theorem ramPolytime_print : RamPolytime print := by
  refine Lax470956Proofs.RamBridge.ramPolytime_of_poly (c := 100) (d := 1) (K := 9)
    (prog := prog) (Polynomial.C 8221 * (Polynomial.X + Polynomial.C 1) ^ 3)
    (by omega) (by norm_num) ?_ ?_
  · intro x v hv
    have h1 := print_le_one hv
    have h2 : 2 ≤ 2 ^ (1 * bitSize x + 9) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) (show 1 ≤ 1 * bitSize x + 9 by omega))
    omega
  · intro w x hfits
    have hy : (x.length :: x) ∈ Shape := ⟨by simp, by simp⟩
    have hf : Lax470956.ParameterizedComplexity.Fits 100 w (x.length :: x) := by
      intro v hv
      simpa using hfits v hv
    obtain ⟨t, ht, hrun⟩ := prog_computesInTime w (x.length :: x) ⟨hy, hf⟩
    refine ⟨t, ?_, by simpa using hrun⟩
    have := Kc_le x
    simp only [List.tail_cons] at ht
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

end Lax470956Proofs.PrintRam
