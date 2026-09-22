import Mathlib.Tactic

/-!
Configurations as table indices.

A configuration of `m` machines, each free for at most `P` units, is a number in base
`P + 1` with `m` digits. This file is the dictionary: the number of a configuration, the
digits of a number, and the two edits the sweep performs — zeroing one digit, and
advancing every digit.
-/

namespace Lax470956Proofs.Radix

private lemma Nat.pos_pow_of_pos' {a b : ℕ} (h : 0 < a) : 0 < a ^ b := Nat.pow_pos h

variable {P m : ℕ} {u : ℕ → ℕ}

/-- The number of the configuration `u`. -/
def enc (P m : ℕ) (u : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range m, u i * (P + 1) ^ i

/-- The `i`-th digit of `c`. -/
def dig (P c i : ℕ) : ℕ := c / (P + 1) ^ i % (P + 1)

lemma enc_congr {u v : ℕ → ℕ} (h : ∀ i, i < m → u i = v i) : enc P m u = enc P m v :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

@[simp] def enc_zero (u : ℕ → ℕ) : enc P 0 u = 0 := rfl

lemma enc_succ (u : ℕ → ℕ) :
    enc P (m + 1) u = enc P m u + u m * (P + 1) ^ m := Finset.sum_range_succ _ _

lemma enc_lt (hu : ∀ i, i < m → u i ≤ P) : enc P m u < (P + 1) ^ m := by
  induction m with
  | zero => simp [enc]
  | succ m ih =>
      have h1 := ih fun i hi => hu i (by omega)
      have h2 : u m ≤ P := hu m (by omega)
      have hpos : 0 < (P + 1) ^ m := Nat.pos_pow_of_pos' (by omega)
      rw [enc_succ, pow_succ]
      calc enc P m u + u m * (P + 1) ^ m
          < (P + 1) ^ m + u m * (P + 1) ^ m := by omega
        _ = (u m + 1) * (P + 1) ^ m := by ring
        _ ≤ (P + 1) * (P + 1) ^ m := Nat.mul_le_mul_right _ (by omega)
        _ = (P + 1) ^ m * (P + 1) := by ring

/-- The digits of a number are the configuration it encodes. -/
lemma dig_enc (hu : ∀ i, i < m → u i ≤ P) (i : ℕ) (hi : i < m) :
    dig P (enc P m u) i = u i := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge i m with h | h
      · have hlt : enc P m u < (P + 1) ^ m := enc_lt fun k hk => hu k (by omega)
        have hdvd : (P + 1) ^ i ∣ (P + 1) ^ m := pow_dvd_pow _ (le_of_lt h)
        have hkey : enc P (m + 1) u / (P + 1) ^ i % (P + 1)
            = enc P m u / (P + 1) ^ i % (P + 1) := by
          obtain ⟨k, hk⟩ := hdvd
          rw [enc_succ, hk]
          have : u m * ((P + 1) ^ i * k) = ((P + 1) ^ i) * (u m * k) := by ring
          rw [this, Nat.add_mul_div_left _ _ (Nat.pos_pow_of_pos' (by omega))]
          have hk1 : (P + 1) ∣ k := by
            have : (P + 1) ^ i * (P + 1) ∣ (P + 1) ^ i * k := by
              rw [← pow_succ, ← hk]; exact pow_dvd_pow _ (by omega)
            exact (mul_dvd_mul_iff_left (a := (P + 1) ^ i)
              (by positivity)).mp this
          obtain ⟨k', rfl⟩ := hk1
          have : u m * ((P + 1) * k') = (u m * k') * (P + 1) := by ring
          rw [this, Nat.add_mul_mod_self_right]
        rw [dig, hkey]
        exact ih (fun k hk => hu k (by omega)) i h
      · have him : i = m := by omega
        subst him
        have hlt : enc P i u < (P + 1) ^ i := enc_lt fun k hk => hu k (by omega)
        have hpos : 0 < (P + 1) ^ i := Nat.pos_pow_of_pos' (by omega)
        rw [dig, enc_succ, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt,
          Nat.zero_add, Nat.mod_eq_of_lt (by have := hu i (by omega); omega)]

/-- The digits of a number encode its remainder. -/
lemma enc_dig_mod (c : ℕ) : enc P m (dig P c) = c % (P + 1) ^ m := by
  induction m with
  | zero => simp [enc, Nat.mod_one]
  | succ m ih =>
      rw [enc_succ, ih, dig, pow_succ, Nat.mod_mul]
      ring

/-- A number below the table size is the number of its own configuration. -/
lemma enc_dig (c : ℕ) (hc : c < (P + 1) ^ m) : enc P m (dig P c) = c := by
  rw [enc_dig_mod, Nat.mod_eq_of_lt hc]

lemma dig_le (c i : ℕ) : dig P c i ≤ P := by
  have := Nat.mod_lt (c / (P + 1) ^ i) (show 0 < P + 1 by omega)
  simpa [dig] using Nat.lt_succ_iff.mp this

/-- Zeroing one digit subtracts it. -/
lemma enc_update_zero (hu : ∀ i, i < m → u i ≤ P) {i : ℕ} (hi : i < m) :
    enc P m (Function.update u i 0) = enc P m u - u i * (P + 1) ^ i := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have h1 : enc P m u = u i * (P + 1) ^ i
      + ∑ k ∈ (Finset.range m).erase i, u k * (P + 1) ^ k :=
    (Finset.add_sum_erase _ _ hmem).symm
  have h2 : enc P m (Function.update u i 0) = 0 * (P + 1) ^ i
      + ∑ k ∈ (Finset.range m).erase i, u k * (P + 1) ^ k := by
    rw [enc, ← Finset.add_sum_erase _ _ hmem, Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  omega

end Lax470956Proofs.Radix
