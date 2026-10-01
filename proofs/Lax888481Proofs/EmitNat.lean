import Lax888481Proofs.PrintModel
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic

/-!
Writing one number in the self-delimiting binary code, as an IMP+ command.

Three loops: halve the number until it vanishes, counting the steps, which is its length
in bits; write that many ones and a zero; halve it again, writing the low digit each
time. The cost is linear in the length of the number.
-/

namespace Lax888481Proofs.EmitNat

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax888481Proofs.PrintModel

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))
abbrev half (e : Expr) : Expr := .bin .div e (.lit 2)

def sizeBody : Com := .seq (.assign "u" (half (V "u"))) (bump "s")

def sizeLoop : Com :=
  .seq (.assign "s" (.lit 0)) (.seq (.assign "u" (V "v"))
    (.while (.lt (.lit 0) (V "u")) sizeBody))

def onesBody : Com := .seq (.write (.lit 1)) (bump "i2")
def onesLoop : Com := .seq (.assign "i2" (.lit 0)) (.while (.lt (V "i2") (V "s")) onesBody)

def digBody : Com :=
  .seq (.write (.bin .sub (V "u") (.bin .mul (.lit 2) (half (V "u")))))
    (.seq (.assign "u" (half (V "u"))) (bump "i2"))

def digLoop : Com :=
  .seq (.assign "u" (V "v"))
    (.seq (.assign "i2" (.lit 0)) (.while (.lt (V "i2") (V "s")) digBody))

/-- Write the number held in `v`. -/
def emitNat : Com := .seq sizeLoop (.seq onesLoop (.seq (.write (.lit 0)) digLoop))

variable {B : ℕ}

lemma size_half {u : ℕ} (hu : 0 < u) : (u / 2).size + 1 = u.size := by
  have h := Nat.bit_testBit_zero_shiftRight_one u
  have hne : Nat.bit (u.testBit 0) (u >>> 1) ≠ 0 := by rw [h]; omega
  have := Nat.size_bit hne
  rw [h, Nat.shiftRight_one] at this
  omega

theorem sizeBody_spec (n : ℕ) (hB : n + 4 < B) :
    Spec B (fun σ => (σ.vars "v" = n ∧ σ.vars "u" ≤ n ∧ (σ.vars "u").size + σ.vars "s" = n.size)
        ∧ (Cond.lt (.lit 0) (V "u")).evalB B σ = some true) sizeBody
      (fun σ σ' => (σ'.vars "v" = n ∧ σ'.vars "u" ≤ n ∧
          (σ'.vars "u").size + σ'.vars "s" = n.size) ∧
        (σ'.vars "u").size < (σ.vars "u").size) 10 := by
  refine Spec.pre (P := fun σ => σ.vars "v" = n ∧ σ.vars "u" ≤ n ∧
      (σ.vars "u").size + σ.vars "s" = n.size ∧ 0 < σ.vars "u" ∧ n.size ≤ n) ?_ ?_
  · run_vcg
    all_goals have hu := ‹0 < σ.vars "u"›
    all_goals have hsz := size_half hu
    all_goals have hle := ‹σ.vars "u" ≤ n›
    all_goals have hs := ‹(σ.vars "u").size + σ.vars "s" = n.size›
    all_goals have hnn := ‹n.size ≤ n›
    all_goals try simp
    all_goals try (refine ⟨⟨by assumption, by omega, by omega⟩, by omega⟩)
    all_goals omega
  · rintro σ ⟨⟨hv, hle, hs⟩, hc⟩
    have hu : 0 < σ.vars "u" := by
      have := Cond.eval_of_evalB hc
      simpa [Cond.eval, Expr.eval] using this
    exact ⟨hv, hle, hs, hu, Nat.size_le.mpr Nat.lt_two_pow_self⟩

/-- The invariant of the halving loop. -/
def SInv (n : ℕ) (σ : Env) : Prop :=
  σ.vars "v" = n ∧ σ.vars "u" ≤ n ∧ (σ.vars "u").size + σ.vars "s" = n.size

lemma cond_def (n : ℕ) (hB : n + 4 < B) (σ : Env) (h : SInv n σ) :
    ∃ v, (Cond.lt (.lit 0) (V "u")).evalB B σ = some v := by
  have hu : σ.vars "u" < B := by have := h.2.1; omega
  exact ⟨decide (0 < σ.vars "u"), by
    simp [Cond.evalB, evalB_lit (show 0 < B by omega), evalB_var hu]⟩

theorem sizeWhile_spec (n : ℕ) (hB : n + 4 < B) :
    Spec B (SInv n) (.while (.lt (.lit 0) (V "u")) sizeBody)
      (fun _ σ' => σ'.vars "v" = n ∧ σ'.vars "s" = n.size) (14 * n.size + 4) := by
  refine (Spec.while_count (SInv n) (fun σ => (σ.vars "u").size) 10 (cond_def n hB)
    (sizeBody_spec n hB) (fun _ h => h) (fun σ h => ?_)).post ?_
  · have hle : (σ.vars "u").size ≤ n.size := by have := h.2.2; omega
    have : (1 + (Cond.lt (.lit 0) (V "u")).size + 10) * (σ.vars "u").size
        ≤ 14 * n.size := by
      simp only [show (Cond.lt (.lit 0) (V "u")).size = 3 from rfl]
      exact Nat.mul_le_mul_left 14 hle
    simp only [show (Cond.lt (.lit 0) (V "u")).size = 3 from rfl] at this ⊢
    omega
  · rintro σ σ' - ⟨⟨hv, hle, hs⟩, hf⟩
    have hu : ¬ 0 < σ'.vars "u" := by
      have := Cond.eval_of_evalB hf
      simpa [Cond.eval, Expr.eval] using this
    have hz : σ'.vars "u" = 0 := by omega
    rw [hz] at hs
    simp at hs
    exact ⟨hv, hs⟩

theorem sizeLoop_spec (n : ℕ) (hB : n + 4 < B) :
    Spec B (fun σ => σ.vars "v" = n) sizeLoop
      (fun _ σ' => σ'.vars "v" = n ∧ σ'.vars "s" = n.size) (14 * n.size + 12) := by
  run_vcg [sizeWhile_spec n hB]
  all_goals have hv := ‹σ.vars "v" = n›
  all_goals try simp [SInv, hv]
  all_goals try omega
  all_goals try assumption

/-! ### The Unary Length -/

def OInv (n : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "v" = n ∧ σ.vars "s" = n.size ∧ σ.vars "i2" ≤ n.size ∧
    σ.out = out0 ++ List.replicate (σ.vars "i2") 1

theorem onesBody_spec (n : ℕ) (out0 : List ℕ) (hB : n + 4 < B) :
    Spec B (fun σ => OInv n out0 σ ∧ σ.vars "i2" < n.size) onesBody
      (fun σ σ' => OInv n out0 σ' ∧ σ'.vars "i2" = σ.vars "i2" + 1) 6 := by
  have hsz : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  run_vcg
  all_goals obtain ⟨hv, hs, hi, hout⟩ := ‹OInv n out0 σ›
  all_goals try simp [OInv, hv, hs, hout, List.replicate_succ']
  all_goals omega

theorem onesLoop_spec (n : ℕ) (out0 : List ℕ) (hB : n + 4 < B) :
    Spec B (fun σ => OInv n out0 (σ.setVar "i2" 0)) onesLoop
      (fun _ σ' => OInv n out0 σ' ∧ σ'.vars "i2" = n.size) (10 * n.size + 6) :=
  Spec.forRangeZero "i2" "s" (OInv n out0) n.size 6
    (by have : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self; omega)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (onesBody_spec n out0 hB)

/-! ### The Digits -/

def DInv (n : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "v" = n ∧ σ.vars "s" = n.size ∧ σ.vars "i2" ≤ n.size ∧
    σ.vars "u" = n / 2 ^ σ.vars "i2" ∧
    σ.out = out0 ++ (List.range (σ.vars "i2")).map (digit n)

theorem digBody_spec (n : ℕ) (out0 : List ℕ) (hB : n + 4 < B) :
    Spec B (fun σ => DInv n out0 σ ∧ σ.vars "i2" < n.size) digBody
      (fun σ σ' => DInv n out0 σ' ∧ σ'.vars "i2" = σ.vars "i2" + 1) 20 := by
  have hsz : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  refine Spec.pre (P := fun σ => DInv n out0 σ ∧ σ.vars "i2" < n.size ∧ σ.vars "u" ≤ n) ?_ ?_
  · run_vcg
    all_goals obtain ⟨hv, hs, hi, hu, hout⟩ := ‹DInv n out0 σ›
    all_goals have hule := ‹σ.vars "u" ≤ n›
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [hv, hs]
      · omega
      · rw [hu, Nat.div_div_eq_div_mul, pow_succ]
      · rw [hout, List.range_succ, List.map_append, List.append_assoc]
        congr 2
        simp only [List.map_cons, List.map_nil, digit, hu]
        congr 1
        omega
    all_goals try simp
    all_goals omega
  · rintro σ ⟨hI, hlt⟩
    exact ⟨hI, hlt, by rw [hI.2.2.2.1]; exact Nat.div_le_self _ _⟩

theorem digWhile_spec (n : ℕ) (out0 : List ℕ) (hB : n + 4 < B) :
    Spec B (fun σ => DInv n out0 (σ.setVar "i2" 0))
      (.seq (.assign "i2" (.lit 0)) (.while (.lt (V "i2") (V "s")) digBody))
      (fun _ σ' => DInv n out0 σ' ∧ σ'.vars "i2" = n.size) (24 * n.size + 6) :=
  Spec.forRangeZero "i2" "s" (DInv n out0) n.size 20
    (by have : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self; omega)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (digBody_spec n out0 hB)

/-! ### The Whole Number -/

theorem emitNat_ghost (n : ℕ) (out0 : List ℕ) (hB : n + 4 < B) :
    Spec B (fun σ => σ.vars "v" = n ∧ σ.out = out0) emitNat
      (fun _ σ' => σ'.out = out0 ++ bitsNat n) (48 * n.size + 40) := by
  have hnw : sizeLoop.NoWrite := by simp [sizeLoop, sizeBody, Com.NoWrite]
  run_vcg [(sizeLoop_spec n hB).frame, onesLoop_spec n out0 hB,
    digWhile_spec n (out0 ++ List.replicate n.size 1 ++ [0]) hB]
  all_goals try simp only [OInv, DInv] at *
  all_goals try (simp_all [bitsNat]; done)
  all_goals try (simp_all [bitsNat]; omega)

/-- **Writing a number.** The output grows by the number's code, at a cost linear in its
length; nothing is said of the scalars the command uses, which a caller reads off
`Spec.frame`. -/
theorem emitNat_spec (S : ℕ) :
    Spec B (fun σ => σ.vars "v" + 4 < B ∧ (σ.vars "v").size ≤ S) emitNat
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (σ.vars "v")) (48 * S + 40) := by
  intro σ ⟨hB, hS⟩
  obtain ⟨σ', hrun, hout⟩ := emitNat_ghost (σ.vars "v") σ.out hB σ ⟨rfl, rfl⟩
  exact ⟨σ', hrun.mono (by omega), hout⟩

end Lax888481Proofs.EmitNat
