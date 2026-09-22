import Lax470956Proofs.Construction1Shape
import Lax470956.Construction1
import Mathlib.Data.List.Sort

/-!
The edge list, as one scan of the word.

Construction 1 numbers its edge jobs by the enumeration `edgeList`: the pairs `(u, v)`
with `u` adjacent to `v` and of smaller colour, in lexicographic order. That is a
definition about the graph. The program has only the word, and what it can do in linear
time is walk the target array once, keeping track of which vertex owns the slot it is
looking at, and keep the slots whose target has a larger colour than their owner.

This file shows the two are the same list. The adjacency lists are strictly increasing
and the owner of a slot never decreases, so the scan meets the pairs in lexicographic
order and meets none twice; and it meets exactly the adjacent pairs, because a block
lists exactly the neighbours of its vertex. Two strictly increasing lists with the same
members are equal.
-/

namespace Lax470956Proofs.Construction1Edges

open Lax470956.MulticolouredClique Lax470956.Construction1
open Lax470956Proofs.Construction1Shape

/-- Lexicographic order on pairs of numbers. -/
def lexLt (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

lemma lexLt_asymm {p q : ℕ × ℕ} (h : lexLt p q) (h' : lexLt q p) : p = q := by
  rcases h with h | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h1', h2'⟩ <;> omega

lemma lexLt_irrefl (p : ℕ × ℕ) : ¬ lexLt p p := by
  rintro (h | ⟨-, h⟩) <;> omega

/-- Two strictly increasing lists with the same members are equal. -/
lemma eq_of_lex {l₁ l₂ : List (ℕ × ℕ)} (h₁ : l₁.Pairwise lexLt) (h₂ : l₂.Pairwise lexLt)
    (hmem : ∀ p, p ∈ l₁ ↔ p ∈ l₂) : l₁ = l₂ := by
  have d₁ : l₁.Nodup := h₁.imp fun {a b} hab he => by subst he; exact lexLt_irrefl a hab
  have d₂ : l₂.Nodup := h₂.imp fun {a b} hab he => by subst he; exact lexLt_irrefl a hab
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => lexLt_asymm hab hba) h₁ h₂
    ((List.perm_ext_iff_of_nodup d₁ d₂).mpr hmem)

variable (x : List ℕ)

/-- The owner of slot `t`: the number of blocks that end at or before it. -/
def own (t : ℕ) : ℕ :=
  ((List.range (vn x)).filter fun i => decide (off x (i + 1) ≤ t)).length

/-- The pairs the scan has kept after `t` slots. -/
def acc (t : ℕ) : List (ℕ × ℕ) :=
  ((List.range t).filter fun s => decide (colr x (own x s) < colr x (tgt x s))).map
    fun s => (own x s, tgt x s)

variable {x}

lemma acc_succ (t : ℕ) :
    acc x (t + 1) = acc x t ++
      (if colr x (own x t) < colr x (tgt x t) then [(own x t, tgt x t)] else []) := by
  simp only [acc, List.range_succ, List.filter_append, List.map_append]
  split_ifs with h <;> simp [h]

@[simp] def acc_zero : acc x 0 = [] := rfl

lemma length_filter_lt_range {u n : ℕ} (h : u ≤ n) :
    ((List.range n).filter fun i => decide (i < u)).length = u := by
  induction n with
  | zero => have : u = 0 := by omega
            subst this; simp
  | succ p ih =>
      rw [List.range_succ, List.filter_append, List.length_append]
      rcases Nat.lt_or_ge u (p + 1) with hlt | hge
      · have : ¬ p < u := by omega
        simp [this, ih (by omega)]
      · have hu : u = p + 1 := by omega
        subst hu
        have hf : (List.range p).filter (fun i => decide (i < p + 1)) = List.range p :=
          List.filter_eq_self.mpr fun a ha => by
            have := List.mem_range.mp ha
            simp; omega
        simp [hf]

variable {G : Instance} (hR : Reads x G)
include hR

/-- The offsets are nondecreasing along the whole array. -/
lemma off_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ vn x) : off x i ≤ off x j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_refl _
  | succ p ih =>
      rcases Nat.lt_or_ge i (p + 1) with hlt | hge
      · exact le_trans (ih (by omega) (by omega)) (hR.off_mono p (by omega))
      · have : i = p + 1 := by omega
        subst this; exact le_refl _

/-- **The owner of a slot is the vertex whose block contains it.** -/
lemma own_eq {u t : ℕ} (hu : u < vn x) (h1 : off x u ≤ t) (h2 : t < off x (u + 1)) :
    own x t = u := by
  have hcongr : (List.range (vn x)).filter (fun i => decide (off x (i + 1) ≤ t))
      = (List.range (vn x)).filter (fun i => decide (i < u)) := by
    refine List.filter_congr fun i hi => ?_
    have hin := List.mem_range.mp hi
    rcases Nat.lt_or_ge i u with h | h
    · have := off_mono hR (i := i + 1) (j := u) (by omega) (by omega)
      simp [h]; omega
    · have := off_mono hR (i := u + 1) (j := i + 1) (by omega) (by omega)
      have h' : ¬ i < u := by omega
      simp [h']; omega
  rw [own, hcongr, length_filter_lt_range (by omega)]

/-- Every slot has an owner. -/
lemma exists_owner {t : ℕ} (ht : t < 2 * ve x) :
    ∃ u, u < vn x ∧ off x u ≤ t ∧ t < off x (u + 1) := by
  have hex : ∃ i, i < vn x ∧ t < off x (i + 1) := by
    have hpos : 0 < vn x := by
      by_contra hc
      have h0 : vn x = 0 := by omega
      have := hR.off_last
      rw [h0, hR.off_zero] at this
      omega
    exact ⟨vn x - 1, by omega, by
      rw [show vn x - 1 + 1 = vn x by omega, hR.off_last]; exact ht⟩
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, hR.off_zero]; omega
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    have hlt := (Nat.find_spec hex).1
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hmin
    by_contra hc
    exact hmin ⟨by omega, by omega⟩

lemma own_spec {t : ℕ} (ht : t < 2 * ve x) :
    own x t < vn x ∧ off x (own x t) ≤ t ∧ t < off x (own x t + 1) := by
  obtain ⟨u, hu, h1, h2⟩ := exists_owner hR ht
  rw [own_eq hR hu h1 h2]
  exact ⟨hu, h1, h2⟩

/-- Within a block the targets increase strictly. -/
lemma tgt_lt_tgt {u s₁ s₂ : ℕ} (hu : u < vn x) (h1 : off x u ≤ s₁) (h12 : s₁ < s₂)
    (h2 : s₂ < off x (u + 1)) : tgt x s₁ < tgt x s₂ := by
  induction s₂ with
  | zero => omega
  | succ p ih =>
      rcases Nat.lt_or_ge s₁ p with hlt | hge
      · exact lt_trans (ih hlt (by omega)) (hR.tgt_sorted u hu p (by omega) h2)
      · have : s₁ = p := by omega
        subst this
        exact hR.tgt_sorted u hu s₁ h1 h2

/-- The scan meets the pairs in strictly increasing order. -/
lemma acc_pairwise (t : ℕ) (ht : t ≤ 2 * ve x) : (acc x t).Pairwise lexLt := by
  rw [acc, List.pairwise_map]
  refine List.Pairwise.filter _ ?_
  refine (List.pairwise_lt_range (n := t)).imp_of_mem ?_
  intro s₁ s₂ hs₁ hs₂ h12
  have hs₂' := List.mem_range.mp hs₂
  obtain ⟨hu₁, ha₁, hb₁⟩ := own_spec hR (t := s₁) (by omega)
  obtain ⟨hu₂, ha₂, hb₂⟩ := own_spec hR (t := s₂) (by omega)
  rcases Nat.lt_trichotomy (own x s₁) (own x s₂) with h | h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    exact tgt_lt_tgt hR hu₁ ha₁ h12 (by rw [h]; exact hb₂)
  · exfalso
    have := off_mono hR (i := own x s₂ + 1) (j := own x s₁) (by omega) (by omega)
    omega

/-- The edge enumeration, as pairs of numbers. -/
noncomputable def edgePairs (G : Instance) : List (ℕ × ℕ) :=
  (edgeList G).map fun p => ((p.1 : ℕ), (p.2 : ℕ))

omit hR in
lemma edgePairs_pairwise (G : Instance) : (edgePairs G).Pairwise lexLt := by
  classical
  rw [edgePairs, List.pairwise_map, edgeList]
  refine List.Pairwise.filter _ ?_
  show List.Pairwise _ (List.product _ _)
  rw [List.product, List.pairwise_flatMap]
  refine ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp fun {b c} hbc => Or.inr ⟨rfl, hbc⟩
  · refine (List.pairwise_lt_finRange _).imp fun {a b} hab p hp q hq => ?_
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
    exact Or.inl hab

omit hR in
lemma mem_edgePairs {G : Instance} {p : ℕ × ℕ} :
    p ∈ edgePairs G ↔ ∃ u v : Fin G.vertices, (G.colour u : ℕ) < (G.colour v : ℕ) ∧
      G.graph.Adj u v ∧ p = ((u : ℕ), (v : ℕ)) := by
  classical
  simp only [edgePairs, edgeList, List.mem_map, List.mem_filter, decide_eq_true_eq,
    List.pair_mem_product, List.mem_finRange, true_and, Prod.exists]
  constructor
  · rintro ⟨u, v, ⟨-, h1, h2⟩, rfl⟩
    exact ⟨u, v, h1, h2, rfl⟩
  · rintro ⟨u, v, h1, h2, rfl⟩
    exact ⟨u, v, ⟨by simp, h1, h2⟩, rfl⟩

/-- **The scan of the whole target array is the edge enumeration.** -/
theorem acc_eq_edgePairs : acc x (2 * ve x) = edgePairs G := by
  refine eq_of_lex (acc_pairwise hR _ (le_refl _)) (edgePairs_pairwise G) fun p => ?_
  rw [mem_edgePairs]
  simp only [acc, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨s, ⟨hs, hc⟩, rfl⟩
    obtain ⟨hu, ha, hb⟩ := own_spec hR hs
    have hv := hR.tgt_lt s hs
    have hu' : own x s < G.vertices := by rw [← hR.vn_eq]; exact hu
    have hv' : tgt x s < G.vertices := by rw [← hR.vn_eq]; exact hv
    refine ⟨⟨own x s, hu'⟩, ⟨tgt x s, hv'⟩, ?_, ?_, rfl⟩
    · rw [← hR.colr_eq ⟨own x s, hu'⟩, ← hR.colr_eq ⟨tgt x s, hv'⟩]; exact hc
    · exact (hR.adj_iff ⟨own x s, hu'⟩ ⟨tgt x s, hv'⟩).mpr ⟨s, ha, hb, rfl⟩
  · rintro ⟨u, v, hc, hadj, rfl⟩
    obtain ⟨s, ha, hb, hs⟩ := (hR.adj_iff u v).mp hadj
    have hu : (u : ℕ) < vn x := by rw [hR.vn_eq]; exact u.isLt
    have hown := own_eq hR hu ha hb
    have hslt : s < 2 * ve x := by
      have := off_mono hR (i := (u : ℕ) + 1) (j := vn x) (by omega) (le_refl _)
      rw [hR.off_last] at this
      omega
    refine ⟨s, ⟨hslt, ?_⟩, by rw [hown, hs]⟩
    rw [hown, hs, hR.colr_eq u, hR.colr_eq v]
    exact hc

end Lax470956Proofs.Construction1Edges
