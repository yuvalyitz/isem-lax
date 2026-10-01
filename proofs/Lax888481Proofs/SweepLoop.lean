import Lax888481Proofs.SweepDP

/-!
The sweep's outer loop: the blocks.

The order pass hands the sweep a list of jobs, cut into blocks. This file is the
bookkeeping: what the running total means at each point, and why the totals of the
blocks add up to the optimum of the instance.
-/

namespace Lax888481Proofs.SweepLoop

open Lax888481.Scheduling Lax888481.Scheduling.Instance Lax888481.Preprocessing
open Lax888481.DynamicProgram (optimum)
open Lax888481Proofs.FreeDP Lax888481Proofs.SweepDP

variable {I : Instance} {P : ℕ}

/-- The jobs `ord a, …, ord (b-1)`. -/
def seg (ord : ℕ → Fin I.jobs) (a b : ℕ) : List (Fin I.jobs) :=
  (List.range (b - a)).map fun i => ord (a + i)

@[simp] lemma seg_self (ord : ℕ → Fin I.jobs) (a : ℕ) : seg ord a a = [] := by simp [seg]

lemma seg_succ (ord : ℕ → Fin I.jobs) {a b : ℕ} (h : a ≤ b) :
    seg ord a (b + 1) = seg ord a b ++ [ord b] := by
  unfold seg
  rw [show b + 1 - a = (b - a) + 1 by omega, List.range_succ, List.map_append]
  simp [Nat.add_sub_cancel' h]

lemma mem_seg {ord : ℕ → Fin I.jobs} {a b : ℕ} {x : Fin I.jobs} :
    x ∈ seg ord a b ↔ ∃ i, a ≤ i ∧ i < b ∧ ord i = x := by
  simp only [seg, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨a + i, by omega, by omega, rfl⟩
  · rintro ⟨i, h1, h2, rfl⟩; exact ⟨i - a, by omega, by rw [show a + (i - a) = i by omega]⟩

lemma seg_length (ord : ℕ → Fin I.jobs) (a b : ℕ) : (seg ord a b).length = b - a := by
  simp [seg]

/-- The index at which the block holding job `k-1` began. -/
def cut (nc : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if nc k then k else cut nc k

lemma cut_le (nc : ℕ → Bool) : ∀ k, cut nc k ≤ k
  | 0 => le_refl _
  | k + 1 => by
      rw [cut]
      split
      · omega
      · exact le_trans (cut_le nc k) (by omega)

lemma cut_succ_le (nc : ℕ → Bool) (k : ℕ) : cut nc (k + 1) ≤ k := by
  rw [cut]; split
  · exact le_refl _
  · exact cut_le nc k

lemma cut_succ_true {nc : ℕ → Bool} {k : ℕ} (h : nc k = true) : cut nc (k + 1) = k := by
  rw [cut, if_pos h]

lemma cut_succ_false {nc : ℕ → Bool} {k : ℕ} (h : nc k = false) : cut nc (k + 1) = cut nc k := by
  rw [cut, if_neg (by simp [h])]

/-- What the order pass promises the sweep. -/
structure Order (I : Instance) (P n : ℕ) (ord : ℕ → Fin I.jobs) (dl : ℕ → ℕ)
    (nc : ℕ → Bool) : Prop where
  /-- Every processing time is at most `P`. -/
  pmax : ∀ j, I.p j ≤ P
  /-- The list has one entry per job. -/
  len : n = I.jobs
  /-- Distinct positions carry distinct jobs. -/
  inj : ∀ a b, a < n → b < n → ord a = ord b → a = b
  /-- The deadlines are the ones recorded. -/
  dl_eq : ∀ k, k < n → dl k = I.d (ord k)
  /-- Inside a block the deadlines do not decrease. -/
  mono : ∀ k, k < n → nc k = false → 0 < k → dl (k - 1) ≤ dl k
  /-- The first job starts a block. -/
  cut0 : nc 0 = true
  /-- A block boundary separates: nothing before it overlaps anything after it. -/
  sep : ∀ k, k < n → nc k = true → ∀ a, a < k → ∀ b, k ≤ b → b < n →
    ¬ I.Overlap (ord a) (ord b)

variable {n : ℕ} {ord : ℕ → Fin I.jobs} {dl : ℕ → ℕ} {nc : ℕ → Bool}

lemma nc_cut (h : Order I P n ord dl nc) : ∀ k, 0 < k → nc (cut nc k) = true := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
      intro _
      by_cases hk : nc k = true
      · rw [cut_succ_true hk]; exact hk
      · rw [cut_succ_false (by simpa using hk)]
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · simpa [cut] using h.cut0
        · exact ih hpos

lemma seg_nodup (h : Order I P n ord dl nc) {a b : ℕ} (hb : b ≤ n) :
    (seg ord a b).Nodup := by
  rw [seg, List.nodup_map_iff_inj_on (List.nodup_range)]
  intro x hx y hy hxy
  simp only [List.mem_range] at hx hy
  have := h.inj (a + x) (a + y) (by omega) (by omega) hxy
  omega

lemma seg_ord (h : Order I P n ord dl nc) {a b : ℕ} (hb : b ≤ n) (hab : a ≤ b)
    (hcut : ∀ k, a < k → k < b → nc k = false) : FreeDP.Ord I (seg ord a b) := by
  unfold FreeDP.Ord
  rw [seg, List.pairwise_map]
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_
  simp only [List.length_range] at hi hj
  simp only [List.getElem_range]
  have hstep : ∀ k, a + i ≤ k → k < a + j → dl k ≤ dl (k + 1) := by
    intro k h1 h2
    have := h.mono (k + 1) (by omega) (hcut (k + 1) (by omega) (by omega)) (by omega)
    simpa using this
  have hmono : ∀ p q, a + i ≤ p → p ≤ q → q ≤ a + j → dl p ≤ dl q := by
    intro p q h1 h2 h3
    induction q with
    | zero =>
        have hp0 : p = 0 := by omega
        subst hp0
        exact le_refl _
    | succ q ihq =>
        rcases Nat.eq_or_lt_of_le h2 with rfl | hlt
        · exact le_refl _
        · exact le_trans (ihq (by omega) (by omega)) (hstep q (by omega) (by omega))
  have h1 := hmono (a + i) (a + j) (le_refl _) (by omega) (le_refl _)
  rw [h.dl_eq (a + i) (by omega), h.dl_eq (a + j) (by omega)] at h1
  exact h1

lemma cut_gap (nc : ℕ → Bool) : ∀ k k', cut nc k < k' → k' < k → nc k' = false := by
  intro k
  induction k with
  | zero => intro k' _ h2; omega
  | succ k ih =>
      intro k' h1 h2
      by_cases hk : nc k = true
      · rw [cut_succ_true hk] at h1; omega
      · rw [cut_succ_false (by simpa using hk)] at h1
        rcases Nat.lt_or_ge k' k with hlt | hge
        · exact ih k' h1 hlt
        · have : k' = k := by omega
          subst this
          simpa using hk

/-- **The blocks add up.** -/
lemma optimumOn_split (h : Order I P n ord dl nc) {k : ℕ} (hk : k ≤ n) (hpos : 0 < k) :
    optimumOn I (seg ord 0 k).toFinset
      = optimumOn I (seg ord 0 (cut nc k)).toFinset
        + optimumOn I (seg ord (cut nc k) k).toFinset := by
  set q := cut nc k with hq
  have hqk : q ≤ k := cut_le nc k
  have hunion : (seg ord 0 k).toFinset
      = (seg ord 0 q).toFinset ∪ (seg ord q k).toFinset := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_union, mem_seg]
    constructor
    · rintro ⟨i, -, h2, rfl⟩
      rcases Nat.lt_or_ge i q with hlt | hge
      · exact Or.inl ⟨i, by omega, by omega, rfl⟩
      · exact Or.inr ⟨i, by omega, by omega, rfl⟩
    · rintro (⟨i, h1, h2, rfl⟩ | ⟨i, h1, h2, rfl⟩) <;> exact ⟨i, by omega, by omega, rfl⟩
  have hdisj : Disjoint (seg ord 0 q).toFinset (seg ord q k).toFinset := by
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    simp only [List.mem_toFinset, mem_seg] at hx hx'
    obtain ⟨i, -, hi2, rfl⟩ := hx
    obtain ⟨i', hi'1, hi'2, hii⟩ := hx'
    have := h.inj i' i (by omega) (by omega) hii
    omega
  have hno : ∀ x ∈ (seg ord 0 q).toFinset, ∀ y ∈ (seg ord q k).toFinset,
      ¬ I.Overlap x y := by
    intro x hx y hy
    simp only [List.mem_toFinset, mem_seg] at hx hy
    obtain ⟨i, -, hi2, rfl⟩ := hx
    obtain ⟨i', hi'1, hi'2, rfl⟩ := hy
    exact h.sep q (by omega) (nc_cut h k hpos) i (by omega) i' (by omega) (by omega)
  rw [hunion, optimumOn_union hdisj hno]

/-- The split, with the empty case folded in. -/
lemma optimumOn_split' (h : Order I P n ord dl nc) {k : ℕ} (hk : k ≤ n) :
    optimumOn I (seg ord 0 k).toFinset
      = optimumOn I (seg ord 0 (cut nc k)).toFinset
        + optimumOn I (seg ord (cut nc k) k).toFinset := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [cut, FreeDP.optimumOn_empty]
  · exact optimumOn_split h hk hpos

/-- At the end, the blocks cover the instance. -/
lemma optimumOn_full (h : Order I P n ord dl nc) :
    optimumOn I (seg ord 0 n).toFinset = optimum I := by
  have huniv : (seg ord 0 n).toFinset = Finset.univ := by
    refine Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) ?_)
    have hnd : (seg ord 0 n).Nodup := seg_nodup h (le_refl n)
    rw [List.toFinset_card_of_nodup hnd, seg_length]
    simp [h.len]
  rw [huniv, optimumOn, optimum]
  congr 1
  exact Finset.filter_congr fun σ _ => by simp

end Lax888481Proofs.SweepLoop
