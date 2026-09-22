import Lax470956Proofs.Radix
import Lax470956.Scheduling

/-!
Schedules as odometer readings.

The sweep needs a table indexed by machine configurations, and on a word whose table
does not fit into memory it cannot run at all. What is left in that case is to try every
schedule. This file is the dictionary for that: a schedule is a string of `n` digits in
base `m + 1`, digit `0` meaning "rejected" and digit `i + 1` meaning "on machine `i`",
so the schedules are exactly the numbers below `(m + 1) ^ n`.

Nothing here mentions the machine. The three facts the program will need are that every
schedule is some number's reading (`hasWeight_iff_exists`), that feasibility is the two
scans the program performs (`feasible_iff`), and that accumulating the weight with a cap
at `W` decides `W ≤ weight σ` without ever holding a number larger than `W` plus one
job's weight (`wacc_eq`, `le_weight_iff`).
-/

namespace Lax470956Proofs.Brute

open Lax470956.Scheduling Lax470956.Scheduling.Instance

variable {I : Instance}

/-! ### A digit as a machine choice -/

/-- What digit `v` says: `0` rejects the job, `i + 1` puts it on machine `i`. A digit
out of range rejects, so the function is total. -/
def mach (I : Instance) (v : ℕ) : Option (Fin I.machines) :=
  if h : v ≠ 0 ∧ v - 1 < I.machines then some ⟨v - 1, h.2⟩ else none

/-- The digit naming the choice a schedule makes for job `i`. -/
def digOf (σ : I.Schedule) (i : ℕ) : ℕ :=
  if h : i < I.jobs then (σ ⟨i, h⟩).elim 0 (fun k => k.val + 1) else 0

lemma digOf_le (σ : I.Schedule) : ∀ i, i < I.jobs → digOf σ i ≤ I.machines := by
  intro i hi
  rw [digOf, dif_pos hi]
  rcases hs : σ ⟨i, hi⟩ with _ | k
  · simp
  · simp

lemma mach_digOf (σ : I.Schedule) (j : Fin I.jobs) : mach I (digOf σ j.val) = σ j := by
  have hj : digOf σ j.val = (σ j).elim 0 (fun k => k.val + 1) := by
    rw [digOf, dif_pos j.isLt, Fin.eta]
  rcases hs : σ j with _ | k
  · rw [hj, hs]; simp [mach]
  · have hk : k.val + 1 ≠ 0 ∧ k.val + 1 - 1 < I.machines := ⟨by omega, by simp⟩
    rw [hj, hs]
    show mach I (k.val + 1) = some k
    rw [mach, dif_pos hk]
    exact congrArg some (Fin.ext (by simp))

/-! ### A number as a schedule -/

/-- The schedule the number `s` reads off, in base `m + 1`. -/
def schedOf (I : Instance) (s : ℕ) : I.Schedule :=
  fun j => mach I (Radix.dig I.machines s j.val)

/-- The number a schedule reads off. -/
def encOf (σ : I.Schedule) : ℕ := Radix.enc I.machines I.jobs (digOf σ)

lemma encOf_lt (σ : I.Schedule) : encOf σ < (I.machines + 1) ^ I.jobs :=
  Radix.enc_lt (digOf_le σ)

lemma schedOf_encOf (σ : I.Schedule) : schedOf I (encOf σ) = σ := by
  funext j
  rw [schedOf, encOf, Radix.dig_enc (digOf_le σ) j.val j.isLt, mach_digOf]

/-! ### Feasibility as two scans -/

lemma overlap_symm {j j' : Fin I.jobs} (h : I.Overlap j j') : I.Overlap j' j := ⟨h.2, h.1⟩

/-- `Feasible` in the shape the program checks it: one pass over the jobs for
eligibility, and one pass over the ordered pairs for the machine clashes. -/
lemma feasible_iff (σ : I.Schedule) :
    Feasible σ ↔
      ((∀ j : Fin I.jobs, ∀ i : Fin I.machines, σ j = some i → i ∈ I.eligible j) ∧
        ∀ a b : Fin I.jobs, a.val < b.val → I.Overlap a b →
          ∀ i : Fin I.machines, σ a = some i → σ b ≠ some i) := by
  constructor
  · rintro ⟨he, hc⟩
    exact ⟨he, fun a b hab hov i ha => hc a b i (by exact fun h => by omega) hov ha⟩
  · rintro ⟨he, hc⟩
    refine ⟨he, fun j j' i hne hov hj => ?_⟩
    rcases Nat.lt_trichotomy j.val j'.val with h | h | h
    · exact hc j j' h hov i hj
    · exact absurd (Fin.ext h) hne
    · intro hj'
      exact hc j' j h (overlap_symm hov) i hj' hj

/-! ### The weight, capped -/

/-- The weight of the first `k` jobs. -/
def wpart (I : Instance) (σ : I.Schedule) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k,
    if h : i < I.jobs then (σ ⟨i, h⟩).elim 0 (fun _ => I.w ⟨i, h⟩) else 0

lemma wpart_jobs (σ : I.Schedule) : wpart I σ I.jobs = weight σ := by
  rw [wpart, weight, ← Fin.sum_univ_eq_sum_range
    (fun i => if h : i < I.jobs then (σ ⟨i, h⟩).elim 0 (fun _ => I.w ⟨i, h⟩) else 0)]
  exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt, Fin.eta]

/-- The accumulator the program runs: the weight so far, never allowed past `W`. -/
def wacc (I : Instance) (σ : I.Schedule) (W : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => min (wacc I σ W k +
      (if h : k < I.jobs then (σ ⟨k, h⟩).elim 0 (fun _ => I.w ⟨k, h⟩) else 0)) W

lemma wacc_eq (σ : I.Schedule) (W : ℕ) : ∀ k, wacc I σ W k = min (wpart I σ k) W
  | 0 => by simp [wacc, wpart]
  | k + 1 => by
      have hk : wacc I σ W k = min (wpart I σ k) W := wacc_eq σ W k
      have hs : wpart I σ (k + 1) = wpart I σ k +
          (if h : k < I.jobs then (σ ⟨k, h⟩).elim 0 (fun _ => I.w ⟨k, h⟩) else 0) := by
        simp only [wpart, Finset.sum_range_succ]
      rw [wacc, hk, hs]
      omega

/-- Capping decides the comparison. -/
lemma le_weight_iff (σ : I.Schedule) (W : ℕ) : W ≤ weight σ ↔ wacc I σ W I.jobs = W := by
  rw [wacc_eq, wpart_jobs]; omega

/-! ### What the enumeration has to find -/

/-- **The brute force is correct**: the instance has a feasible schedule of weight at
least `W` exactly when one of the numbers below `(m + 1) ^ n` reads one off. -/
theorem hasWeight_iff_exists (I : Instance) (W : ℕ) :
    I.HasWeight W ↔ ∃ s < (I.machines + 1) ^ I.jobs,
      Feasible (schedOf I s) ∧ W ≤ weight (schedOf I s) := by
  constructor
  · rintro ⟨σ, hf, hw⟩
    exact ⟨encOf σ, encOf_lt σ, by rw [schedOf_encOf]; exact hf,
      by rw [schedOf_encOf]; exact hw⟩
  · rintro ⟨s, -, hf, hw⟩
    exact ⟨schedOf I s, hf, hw⟩

end Lax470956Proofs.Brute
