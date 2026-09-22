import Lax470956.Construction1
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
The paper's order, as a counting sort.

Construction 1 lays the vertices out in the order `<π` that ranks them by colour and
breaks ties by index, and every processing time and deadline it emits is built from the
rank a vertex has in that order. The definition of `rank` counts, for each vertex, how
many vertices precede it — which is a quadratic amount of work, and the reduction has a
linear budget.

This file proves the identity that makes one pass enough. The rank of `v` splits into
the vertices of a smaller colour, which does not depend on `v` at all but only on its
colour, and the vertices of the same colour with a smaller index, which a single
increasing sweep accumulates. So a count per colour, a prefix sum over the colours, and
one sweep over the vertices produce every rank — the standard counting sort, stated here
as arithmetic so that the program's loop invariants have something to be equal to.

Everything is phrased with `List.range` and `List.filter` rather than with `Finset`,
because that is the shape a counted loop leaves behind.
-/

namespace Lax470956Proofs.Construction1Rank

open Lax470956.MulticolouredClique Lax470956.Construction1

/-! Counting over an initial segment. -/

variable (cf : ℕ → ℕ)

/-- How many of the first `j` vertices have colour `c`. -/
def cntBelow (j c : ℕ) : ℕ := ((List.range j).filter fun u => decide (cf u = c)).length

/-- How many of the first `n` vertices have a colour below `c`. -/
def startAt (n c : ℕ) : ℕ := ((List.range n).filter fun u => decide (cf u < c)).length

/-- How many of the first `n` vertices precede `v` in the paper's order. -/
def before (n v : ℕ) : ℕ :=
  ((List.range n).filter fun u =>
    decide (cf u < cf v ∨ (cf u = cf v ∧ u < v))).length

variable {cf}

/-- One more vertex adds one to the count of its own colour. -/
@[simp] lemma cntBelow_succ (j c : ℕ) :
    cntBelow cf (j + 1) c = cntBelow cf j c + (if cf j = c then 1 else 0) := by
  simp only [cntBelow, List.range_succ, List.filter_append, List.length_append]
  split_ifs with h <;> simp [h]

@[simp] lemma cntBelow_zero (c : ℕ) : cntBelow cf 0 c = 0 := by simp [cntBelow]

/-- The prefix sums of the colour counts. -/
lemma startAt_succ (n c : ℕ) :
    startAt cf n (c + 1) = startAt cf n c + cntBelow cf n c := by
  induction n with
  | zero => simp [startAt, cntBelow]
  | succ p ih =>
      simp only [startAt, cntBelow, List.range_succ, List.filter_append,
        List.length_append] at ih ⊢
      rcases Nat.lt_trichotomy (cf p) c with h | h | h
      · have h1 : cf p < c + 1 := by omega
        have h2 : ¬ (cf p = c) := by omega
        simp [List.filter_cons, List.filter_nil, decide_eq_true_eq, h, h1, h2,
          if_true, if_false, decide_true, decide_false] <;> omega
      · have h1 : cf p < c + 1 := by omega
        have h2 : ¬ (cf p < c) := by omega
        simp [List.filter_cons, List.filter_nil, decide_eq_true_eq, h, h1, h2,
          if_true, if_false, decide_true, decide_false] <;> omega
      · have h1 : ¬ (cf p < c + 1) := by omega
        have h2 : ¬ (cf p < c) := by omega
        have h3 : ¬ (cf p = c) := by omega
        simp [List.filter_cons, List.filter_nil, decide_eq_true_eq, h1, h2, h3,
          if_true, if_false, decide_true, decide_false] <;> omega

@[simp] lemma startAt_zero (n : ℕ) : startAt cf n 0 = 0 := by simp [startAt]

/-- Extending the sweep by one vertex touches the count of its colour, and only while
the sweep is still below `v`. -/
lemma cntBelow_min_succ (p v c : ℕ) :
    cntBelow cf (min (p + 1) v) c
      = cntBelow cf (min p v) c + (if p < v ∧ cf p = c then 1 else 0) := by
  by_cases hpv : p < v
  · have e1 : min (p + 1) v = p + 1 := by omega
    have e2 : min p v = p := by omega
    rw [e1, e2, cntBelow_succ]
    by_cases hc : cf p = c <;> simp [hc, hpv]
  · have e1 : min (p + 1) v = v := by omega
    have e2 : min p v = v := by omega
    rw [e1, e2]
    simp [hpv]

/-- One more vertex in the sweep. -/
@[simp] lemma before_succ (p v : ℕ) :
    before cf (p + 1) v
      = before cf p v + (if cf p < cf v ∨ (cf p = cf v ∧ p < v) then 1 else 0) := by
  simp only [before, List.range_succ, List.filter_append, List.length_append]
  split_ifs with h <;> simp [h]

/-- One more vertex in the colour count. -/
lemma startAt_succ_n (n c : ℕ) :
    startAt cf (n + 1) c = startAt cf n c + (if cf n < c then 1 else 0) := by
  simp only [startAt, List.range_succ, List.filter_append, List.length_append]
  split_ifs with h <;> simp [h]

/-- **The counting sort identity.** A vertex's place in the order is the number of
vertices of a smaller colour, plus the number of earlier vertices of its own colour.

Read as a loop invariant: a sweep that has reached vertex `n` and holds, for each
colour `c`, the value `startAt cf n c + cntBelow cf (min n v) c`, has the rank of every
vertex it has passed. -/
theorem before_eq (n v : ℕ) :
    before cf n v = startAt cf n (cf v) + cntBelow cf (min n v) (cf v) := by
  induction n with
  | zero => simp [before, startAt, cntBelow]
  | succ p ih =>
      rw [before_succ, startAt_succ_n, cntBelow_min_succ, ih]
      split_ifs <;> omega

/-! The sweep the program runs: once over the vertices for every colour. -/

/-- How many of the first `i` steps of the sweep number a vertex: step `j` looks at
vertex `j % n` on behalf of colour `j / n`. -/
def sweep (cf : ℕ → ℕ) (n i : ℕ) : ℕ :=
  ((List.range i).filter fun j => decide (cf (j % n) = j / n)).length

@[simp] lemma sweep_succ (n i : ℕ) :
    sweep cf n (i + 1) = sweep cf n i + (if cf (i % n) = i / n then 1 else 0) := by
  simp only [sweep, List.range_succ, List.filter_append, List.length_append]
  split_ifs with h <;> simp [h]

/-- **The sweep is the counting sort.** When it reaches vertex `v` on behalf of colour
`c` it has numbered the vertices of smaller colour and the earlier ones of colour `c`. -/
theorem sweep_eq {n : ℕ} (c v : ℕ) (hv : v ≤ n) :
    sweep cf n (c * n + v) = startAt cf n c + cntBelow cf v c := by
  induction c generalizing v with
  | zero =>
      induction v with
      | zero => simp [sweep]
      | succ p ih =>
          have hp : p < n := by omega
          have h1 : (0 * n + p) % n = p := by simp [Nat.mod_eq_of_lt hp]
          have h2 : (0 * n + p) / n = 0 := by simp [Nat.div_eq_of_lt hp]
          rw [show 0 * n + (p + 1) = (0 * n + p) + 1 by ring, sweep_succ, ih (by omega),
            h1, h2, cntBelow_succ]
          omega
  | succ d ihd =>
      induction v with
      | zero =>
          rw [show (d + 1) * n + 0 = d * n + n by ring, ihd n (le_refl _), startAt_succ]
          simp
      | succ p ih =>
          have hp : p < n := by omega
          have h1 : ((d + 1) * n + p) % n = p := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
          have h2 : ((d + 1) * n + p) / n = d + 1 := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hp]
            omega
          rw [show (d + 1) * n + (p + 1) = ((d + 1) * n + p) + 1 by ring, sweep_succ,
            ih (by omega), h1, h2, cntBelow_succ]
          omega

/-- The counts only look at the colours of the first `n` vertices. -/
lemma before_congr {cf cf' : ℕ → ℕ} {n v : ℕ} (hv : v < n) (h : ∀ u < n, cf u = cf' u) :
    before cf n v = before cf' n v := by
  simp only [before]
  congr 1
  refine List.filter_congr fun u hu => ?_
  rw [h u (List.mem_range.mp hu), h v hv]

/-! The bridge to the construction's own definition. -/

/-- A count over `List.range` as a sum. -/
lemma length_filter_range (p : ℕ → Bool) (n : ℕ) :
    ((List.range n).filter p).length = ∑ i ∈ Finset.range n, (if p i then 1 else 0) := by
  induction n with
  | zero => simp
  | succ q ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih,
        Finset.sum_range_succ]
      by_cases h : p q <;> simp [h]

/-- A count over `Fin n` is a count over `List.range n`. -/
lemma card_fin_filter (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun u : Fin n => P (u : ℕ)).card
      = ((List.range n).filter fun u => decide (P u)).length := by
  rw [Finset.card_filter, length_filter_range, Fin.sum_univ_eq_sum_range
    (fun i => if P i then 1 else 0) n]
  simp

/-- **The construction's rank is the counting sort's answer.** -/
theorem rank_eq (G : Instance) (v : Fin G.vertices) :
    rank G v = before (fun u => col (G := G) u) G.vertices (v : ℕ) + 1 := by
  classical
  have hcol : ∀ u : Fin G.vertices, col (G := G) (u : ℕ) = (G.colour u : ℕ) :=
    fun u => dif_pos u.isLt
  rw [rank, before, Nat.add_comm]
  congr 1
  rw [← card_fin_filter G.vertices
    (fun u => col (G := G) u < col (G := G) (v : ℕ) ∨
      (col (G := G) u = col (G := G) (v : ℕ) ∧ u < (v : ℕ)))]
  refine congrArg Finset.card (Finset.ext fun u => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcol u, hcol v]

end Lax470956Proofs.Construction1Rank
