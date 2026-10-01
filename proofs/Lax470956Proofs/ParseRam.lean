import Lax470956Proofs.ParseCom
import Lax470956Proofs.PrintRam

/-!
The parser runs in polynomial time on a word RAM.
-/

namespace Lax470956Proofs.ParseRam

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax470956Proofs.ParseModel Lax470956Proofs.ParseSem Lax470956Proofs.ParseScan
open Lax470956Proofs.ParseNames Lax470956Proofs.ParseMain Lax470956Proofs.ParseCom
open Lax470956Proofs.Checker (Shape shape_eq)
open Lax470956Proofs.PrintRam (bnd)

def layout : Layout :=
  ⟨["L", "rt", "rv", "p", "c", "ph", "n", "h", "C", "k", "q", "v", "cnt", "app", "fo", "i",
    "ok"], ["a", "vr", "sg", "nm", "ap"], 8⟩

theorem com_ok : Com.Ok layout ParseCom.com := by
  simp [ParseCom.com, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, scanInit, scanLoop,
    scanBody, dispatch, phase1, phase3, tail, outerLoop, outerBody, outerInit, outerFin,
    innerLoop, innerBody, emitAll, emitLoop, emitBody, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by simp [Layout.const]

def extOf (y : List ℕ) : String → ℕ := fun a => if a = "a" then y.length else y.length + 1

theorem solves : Solves layout ParseCom.com Shape (fun y => parse y.tail) (fun y => bnd y.tail)
    (fun y => Kc y.tail) where
  ok := com_ok
  inp := by
    intro y hy v hv
    have hs := PrintRam.small y.tail
    rw [shape_eq hy] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · have := hs.len; omega
    · have := (hs.entry v hv').1; omega
  run := by
    intro y hy
    have hs := PrintRam.small y.tail
    obtain ⟨σ', hrun, hout⟩ := com_spec (B := bnd y.tail) (y := y.tail)
      (fun v hv => by have := (hs.entry v hv).1; omega) (by have := hs.len; omega)
      (initEnv (extOf y.tail) y)
      ⟨shape_eq hy, rfl, by simp [initEnv, extOf], by simp [initEnv, extOf],
        by simp [initEnv, extOf], by simp [initEnv, extOf], by simp [initEnv, extOf]⟩
    exact ⟨_, σ', hrun, hout⟩

def prog : Program := compileProgram layout ParseCom.com

theorem prog_computesInTime (w : ℕ) :
    ComputesInTime w prog
      {y | y ∈ Shape ∧ Lax470956.ParameterizedComplexity.Fits 400 w y}
      (fun y => parse y.tail) (fun y => 10 * Kc y.tail + 1) := by
  have hs : Solves layout ParseCom.com
      {y | y ∈ Shape ∧ Lax470956.ParameterizedComplexity.Fits 400 w y} (fun y => parse y.tail)
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
    have hbig : 400 * (y.length + y.tail.foldr max 0 + 1) ≤ 2 ^ w := by
      rcases Lax470956Proofs.Pmax.foldr_max_mem_or_zero y.tail with hm | hm
      · exact hfits _ (by rw [shape_eq hsh]; exact List.mem_cons_of_mem _ hm)
      · rw [hm]
        have := hfits _ hne
        omega
    refine fitsWords_of_max_le (by simp only [bnd]; omega) ?_
    simp only [Layout.span, layout, List.length_cons, List.length_nil, bnd, max_le_iff]
    omega
  · rw [const_eq]

/-! ### Polynomial Time, in the Bit-Size Currency -/

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding

lemma word_le {vs ss : List ℕ} {C v : ℕ} (hss : ∀ j < vs.length, ss.getD j 0 ≤ 1)
    (hv : v ∈ word vs ss C) : v ≤ max (max vs.length C) 1 := by
  simp only [word, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range] at hv
  rcases hv with (rfl | rfl) | ⟨k, hk, rfl | rfl | rfl⟩
  · omega
  · omega
  · have := nameOf_lt (vs := vs) hk; omega
  · have := hss k hk; omega
  · have := appOf_le vs k; omega

lemma parse_le {y : List ℕ} {v : ℕ} (hv : v ∈ parse y) : v ≤ y.length + 1 := by
  by_cases h4 : (stAt y y.length).ph = 4
  · by_cases hc : ∀ v ∈ vsAt y, (vsAt y).count v ≤ 4
    · rw [parse_word h4 hc] at hv
      have h1 := word_le ssAt_le hv
      have h2 := vsAt_length_le (y := y)
      have h3 := size_stAt (y := y) y.length
      simp only [ParseScan.size] at h3
      omega
    · rw [parse_nil_of_count h4 hc] at hv; simp at hv
  · rw [parse_nil_of_phase h4] at hv; simp at hv

lemma Kc_le (x : List ℕ) : 10 * Kc x + 1 ≤ 4000 * (bitSize x + 1) ^ 2 := by
  have hlen := length_le_bitSize x
  have hv := vsAt_length_le (y := x)
  set N := bitSize x + 1 with hN
  have hvN : (vsAt x).length ≤ N := by omega
  have hK2 : K2 x ≤ ((44 * N + 6) + 40 + 4) * N + 6 := by unfold K2; gcongr
  have hKE : KE x ≤ 24 * N + 6 := by unfold KE; gcongr
  have hN2 : N ≤ N * N := Nat.le_mul_self N
  have hpow : N ^ 2 = N * N := by ring
  unfold Kc; rw [hpow]
  nlinarith [hK2, hKE, hN2]

/-- **The parser is computable in polynomial time by a word RAM.** -/
theorem ramPolytime_parse : RamPolytime parse := by
  refine Lax470956Proofs.RamBridge.ramPolytime_of_poly (c := 400) (d := 1) (K := 11)
    (prog := prog) (Polynomial.C 4000 * (Polynomial.X + Polynomial.C 1) ^ 2)
    (by omega) (by norm_num) ?_ ?_
  · intro x v hv
    have h1 := parse_le hv
    have h2 := length_le_bitSize x
    have h3 : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
    have h4 : (2:ℕ) ^ (1 * bitSize x + 11) = 2048 * 2 ^ bitSize x := by ring
    omega
  · intro w x hfits
    have hy : (x.length :: x) ∈ Shape := ⟨by simp, by simp⟩
    have hf : Lax470956.ParameterizedComplexity.Fits 400 w (x.length :: x) := by
      intro v hv
      simpa using hfits v hv
    obtain ⟨t, ht, hrun⟩ := prog_computesInTime w (x.length :: x) ⟨hy, hf⟩
    refine ⟨t, ?_, by simpa using hrun⟩
    have := Kc_le x
    simp only [List.tail_cons] at ht
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

end Lax470956Proofs.ParseRam
