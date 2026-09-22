import Lax470956.ParameterizedComplexity
import Lax759944.RamPolytime
import Lax759944Proofs.Encoding

/-!
From a running-time statement in the archive's word RAM style to the polynomial-time
predicate of the RAM/Turing equivalence.

The two say the same thing in different currencies. `Lax808846` measures the input by
its length as a list of numbers and states an explicit bound at every word length that
admits the input; `Lax759944` measures it by its bit size, prefixes the physical input
with its length, and asks for a polynomial. This file converts one into the other once,
so that a program written and costed in the first style can be cited in the second.
-/

namespace Lax470956Proofs.RamBridge

open Lax808846.Ram Lax808846.RamComputes
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax759944Proofs.Encoding

lemma add_two_le_two_pow (s : ℕ) : s + 2 ≤ 2 ^ (s + 1) := by
  have h1 : s < 2 ^ s := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have h3 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
  omega

/-- **The bridge.** A program that, at every word length admitting its length-prefixed
input, computes `f` within `c · (|x| + 2)` instructions, and whose output entries are
words of `bitSize x + K` bits, is a polynomial-time word RAM computation of `f`. -/
theorem ramPolytime_of {f : List ℕ → List ℕ} {prog : Program} {c K : ℕ}
    (hc : 1 ≤ c) (hK : 8 * c ≤ 2 ^ K)
    (hout : ∀ x, ∀ v ∈ f x, v < 2 ^ (bitSize x + K))
    (hrun : ∀ (w : ℕ) (x : List ℕ),
        (∀ v ∈ (x.length :: x), c * ((x.length + 1) + v + 1) ≤ 2 ^ w) →
        ∃ t ≤ c * (x.length + 2), RunsTo w prog (x.length :: x) (f x) t) :
    RamPolytime f := by
  have hK3 : 3 ≤ K := by
    by_contra hcon
    have hKle : K ≤ 2 := by omega
    have h4 : (2 : ℕ) ^ K ≤ 4 := by
      calc (2 : ℕ) ^ K ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hKle
        _ = 4 := rfl
    omega
  refine ⟨prog, Polynomial.X + Polynomial.C K,
    Polynomial.C c * Polynomial.X + Polynomial.C (2 * c), fun x => ⟨?_, ?_⟩⟩
  · intro a ha
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rcases List.mem_append.mp ha with hin | hin
    · have hlt : a < 2 ^ (bitSize x + 1) := by
        rcases List.mem_cons.mp hin with rfl | hin'
        · exact length_lt_two_pow_bitSize_add_one x
        · exact mem_lt_two_pow_bitSize_add_one hin'
      exact hlt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    · exact hout x a hin
  · intro w hw
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hw
    have hfits : ∀ v ∈ (x.length :: x), c * (x.length + 1 + v + 1) ≤ 2 ^ w := by
      intro v hv
      have hvlt : v < 2 ^ (bitSize x + 1) := by
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact length_lt_two_pow_bitSize_add_one x
        · exact mem_lt_two_pow_bitSize_add_one hv'
      have hlen := length_le_bitSize x
      have hs2 := add_two_le_two_pow (bitSize x)
      have hstep : c * (x.length + 1 + v + 1)
          ≤ c * (2 ^ (bitSize x + 1) + 2 ^ (bitSize x + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      have hcalc : c * (2 ^ (bitSize x + 1) + 2 ^ (bitSize x + 1)) ≤ 2 ^ (bitSize x + K) := by
        have e1 : 2 ^ (bitSize x + 1) + 2 ^ (bitSize x + 1) = 4 * 2 ^ (bitSize x) := by ring
        have e2 : 2 ^ (bitSize x + K) = 2 ^ K * 2 ^ (bitSize x) := by ring
        rw [e1, e2, ← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (by omega)
      exact (hstep.trans hcalc).trans (Nat.pow_le_pow_right (by omega) hw)
    obtain ⟨t, ht, hrt⟩ := hrun w x hfits
    refine ⟨t, ?_, hrt⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    have hlen := length_le_bitSize x
    calc t ≤ c * (x.length + 2) := ht
      _ ≤ c * (bitSize x + 2) := Nat.mul_le_mul_left _ (by omega)
      _ = c * bitSize x + 2 * c := by ring

/-- **The bridge, for any polynomial running time.** The same change of currency with the
step count left as a polynomial in the bit size and the fitting condition raised to a
power `d`, as a program with nested loops, whose values and cost are
polynomial rather than linear in the length of its input, needs. -/
theorem ramPolytime_of_poly {f : List ℕ → List ℕ} {prog : Program} {c d K : ℕ}
    (time : Polynomial ℕ)
    (hd : 1 ≤ d) (hK : c * 4 ^ d ≤ 2 ^ K)
    (hout : ∀ x, ∀ v ∈ f x, v < 2 ^ (d * bitSize x + K))
    (hrun : ∀ (w : ℕ) (x : List ℕ),
        (∀ v ∈ (x.length :: x), c * ((x.length + 1) + v + 1) ^ d ≤ 2 ^ w) →
        ∃ t ≤ time.eval (bitSize x), RunsTo w prog (x.length :: x) (f x) t) :
    RamPolytime f := by
  refine ⟨prog, Polynomial.C d * Polynomial.X + Polynomial.C (K + 1), time,
    fun x => ⟨?_, ?_⟩⟩
  · intro a ha
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    rcases List.mem_append.mp ha with hin | hin
    · have hlt : a < 2 ^ (bitSize x + 1) := by
        rcases List.mem_cons.mp hin with rfl | hin'
        · exact length_lt_two_pow_bitSize_add_one x
        · exact mem_lt_two_pow_bitSize_add_one hin'
      calc a < 2 ^ (bitSize x + 1) := hlt
        _ ≤ 2 ^ (d * bitSize x + (K + 1)) := Nat.pow_le_pow_right (by omega) (by
            have : bitSize x ≤ d * bitSize x := Nat.le_mul_of_pos_left _ hd
            omega)
    · calc a < 2 ^ (d * bitSize x + K) := hout x a hin
        _ ≤ 2 ^ (d * bitSize x + (K + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  · intro w hw
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C] at hw
    refine hrun w x fun v hv => ?_
    have hvlt : v < 2 ^ (bitSize x + 1) := by
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact length_lt_two_pow_bitSize_add_one x
      · exact mem_lt_two_pow_bitSize_add_one hv'
    have hlen := length_le_bitSize x
    have hs2 := add_two_le_two_pow (bitSize x)
    have hbase : x.length + 1 + v + 1 ≤ 4 * 2 ^ bitSize x := by
      have e1 : (2:ℕ) ^ (bitSize x + 1) = 2 * 2 ^ bitSize x := by ring
      omega
    calc c * (x.length + 1 + v + 1) ^ d
        ≤ c * (4 * 2 ^ bitSize x) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase d)
      _ = c * 4 ^ d * 2 ^ (d * bitSize x) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (bitSize x) d, Nat.mul_assoc]
      _ ≤ 2 ^ K * 2 ^ (d * bitSize x) := Nat.mul_le_mul_right _ hK
      _ = 2 ^ (d * bitSize x + K) := by rw [← Nat.pow_add, Nat.add_comm]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)

end Lax470956Proofs.RamBridge
