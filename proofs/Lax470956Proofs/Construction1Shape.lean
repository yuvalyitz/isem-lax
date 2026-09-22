import Lax470956Proofs.MccTransfer

/-!
The Multicoloured Clique word, read as the program reads it.

Everything the reduction needs about its input is an entry of the word at a computed
position: the two counts, the `n+1` offsets, the `2m` targets, the `n` colours, and the
number of colours at the end. This file gives those positions names and shows that on a
word that encodes an instance they recover the instance — the vertex count, the
colouring, the adjacency and the parameter.

It is stated this way because the program never has an instance in hand. It
has a tape, and its invariants have to be about entries of that tape; so the arithmetic
identities its correctness rests on are proved here once, against the encoding, and the
program's proof can then be about positions and counters alone.
-/

namespace Lax470956Proofs.Construction1Shape

open Lax470956.MulticolouredClique Lax271696.GraphEncoding

variable (x : List ℕ)

/-- The number of vertices: the first entry. -/
def vn : ℕ := x.getD 0 0

/-- The number of edges: the second entry. -/
def ve : ℕ := x.getD 1 0

/-- The `i`-th offset, of the `n+1` that follow the two counts. -/
def off (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- The `t`-th target, of the `2m` that follow the offsets. -/
def tgt (t : ℕ) : ℕ := x.getD (3 + vn x + t) 0

/-- The colour of vertex `v`, of the `n` that follow the targets. -/
def colr (v : ℕ) : ℕ := x.getD (3 + vn x + 2 * ve x + v) 0

/-- The number of colours: the last entry. -/
def kk : ℕ := x.getD (3 + 2 * vn x + 2 * ve x) 0

variable {x}

/-- The graph block's length, in terms of the whole word. -/
private lemma block_len {g c : List ℕ} {n : ℕ} {A : SimpleGraph (Fin n)}
    (hx : x = g ++ c) (h : EncodesGraph g n A) : g.length = 3 + n + 2 * ve x := by
  have h3 : 3 ≤ g.length := by rw [h.length_eq]; omega
  have hv : g.getD 0 0 = n := h.vertexCount_eq
  have he : ve x = edgeCount g := by
    rw [hx, ve, edgeCount, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  rw [he]; exact h.length_eq

/-- An entry of the graph block is the entry of the word at the same position. -/
private lemma prefix_getD {g c : List ℕ} (hx : x = g ++ c) {i : ℕ} (hi : i < g.length) :
    x.getD i 0 = g.getD i 0 := by
  rw [hx, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

/-- An entry of the middle part of a three-part word. -/
private lemma getD_mid {a b c : List ℕ} {i : ℕ} (hi : i < b.length) :
    (a ++ (b ++ c)).getD (a.length + i) 0 = b.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]

/-- An entry of the last part of a three-part word. -/
private lemma getD_third {a b c : List ℕ} {i : ℕ} (hi : i < c.length) :
    (a ++ (b ++ c)).getD (a.length + b.length + i) 0 = c.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    show a.length + b.length + i = a.length + (b.length + i) by omega,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- The offsets are nondecreasing along the whole array, not only by one step. -/
private lemma offset_mono' {g : List ℕ} {n : ℕ} {A : SimpleGraph (Fin n)}
    (h : EncodesGraph g n A) : ∀ j ≤ n, ∀ i ≤ j, offset g i ≤ offset g j := by
  intro j
  induction j with
  | zero =>
      intro _ i hi
      have : i = 0 := by omega
      subst this; exact le_refl _
  | succ p ih =>
      intro hp i hi
      rcases Nat.lt_or_ge i (p + 1) with hlt | hge
      · exact le_trans (ih (by omega) i (by omega)) (h.offset_mono p (by omega))
      · have : i = p + 1 := by omega
        subst this; exact le_refl _

/-- **What the positions hold on a word that encodes an instance.** -/
structure Reads (x : List ℕ) (G : Instance) : Prop where
  /-- The first entry is the number of vertices. -/
  vn_eq : vn x = G.vertices
  /-- The last entry is the number of colours. -/
  kk_eq : kk x = G.colours
  /-- The word is the two counts, the offsets, the targets, the colours and the
  parameter. -/
  length_eq : x.length = 4 + 2 * vn x + 2 * ve x
  /-- The first block begins at the start of the target array. -/
  off_zero : off x 0 = 0
  /-- The last block ends at its end. -/
  off_last : off x (vn x) = 2 * ve x
  /-- The offsets cut the target array into one block per vertex. -/
  off_mono : ∀ i < vn x, off x i ≤ off x (i + 1)
  /-- Every target is a vertex. -/
  tgt_lt : ∀ t < 2 * ve x, tgt x t < vn x
  /-- The colour positions hold the colouring. -/
  colr_eq : ∀ v : Fin G.vertices, colr x v = (G.colour v : ℕ)
  /-- Each block is strictly increasing. -/
  tgt_sorted : ∀ u < vn x, ∀ t, off x u ≤ t → t + 1 < off x (u + 1) →
    tgt x t < tgt x (t + 1)
  /-- A vertex's block lists exactly its neighbours. -/
  adj_iff : ∀ u v : Fin G.vertices, G.graph.Adj u v ↔
    ∃ t, off x u ≤ t ∧ t < off x (u + 1) ∧ tgt x t = v

/-- **A word that encodes an instance reads as that instance.** -/
theorem reads_of_encodes {G : Instance} (h : EncodesInstance x G) : Reads x G := by
  obtain ⟨g, hx, hg, hsort⟩ := h
  set cl : List ℕ := List.ofFn fun v : Fin G.vertices => (G.colour v : ℕ) with hcl
  have hcllen : cl.length = G.vertices := by simp [hcl]
  have hxa : x = g ++ (cl ++ [G.colours]) := by rw [hx, List.append_assoc]
  have hglen : g.length = 3 + G.vertices + 2 * ve x := block_len hxa hg
  have hvn : vn x = G.vertices := by
    rw [vn, prefix_getD hxa (by omega)]; exact hg.vertexCount_eq
  have hgl : g.length = 3 + vn x + 2 * ve x := by rw [hvn]; exact hglen
  have hec : edgeCount g = ve x := (prefix_getD hxa (i := 1) (by omega)).symm
  -- the three parts of the word, read at positions that do not mention `x`
  have hmid : ∀ i, i < cl.length → x.getD (g.length + i) 0 = cl.getD i 0 :=
    fun i hi => by rw [hxa]; exact getD_mid hi
  have hthird : x.getD (g.length + cl.length + 0) 0 = G.colours := by
    rw [hxa]; exact getD_third (by simp)
  have hxlen : x.length = g.length + (cl.length + 1) := by rw [hxa]; simp
  -- offsets and targets sit inside the graph block
  have hoff : ∀ i, i ≤ vn x → off x i = offset g i := fun i hi => by
    rw [off, offset, prefix_getD hxa (show 2 + i < g.length by omega)]
  have htgt : ∀ t, t < 2 * ve x → tgt x t = target g t := fun t ht => by
    rw [tgt, target, hg.vertexCount_eq, ← hvn,
      prefix_getD hxa (show 3 + vn x + t < g.length by omega)]
  have hmono : ∀ i, i ≤ G.vertices → offset g i ≤ 2 * ve x := fun i hi => by
    have h1 := offset_mono' hg G.vertices (le_refl _) i hi
    rw [hg.offset_last, hec] at h1
    exact h1
  refine ⟨hvn, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kk, show 3 + 2 * vn x + 2 * ve x = g.length + cl.length + 0 by omega]
    exact hthird
  · rw [hoff 0 (by omega)]; exact hg.offset_zero
  · rw [hoff (vn x) (le_refl _), hvn, hg.offset_last, hec]
  · intro i hi
    rw [hoff i (by omega), hoff (i + 1) (by omega)]
    exact hg.offset_mono i (by omega)
  · intro t ht
    rw [htgt t ht, hvn]
    exact hg.target_lt t (by rw [hec]; omega)
  · intro v
    have hlt : (v : ℕ) < cl.length := by rw [hcllen]; exact v.isLt
    rw [colr, show 3 + vn x + 2 * ve x + (v : ℕ) = g.length + (v : ℕ) by omega,
      hmid (v : ℕ) hlt, hcl]
    simp
  · intro u hu t h1 h2
    have hbound : offset g (u + 1) ≤ 2 * ve x := hmono _ (by omega)
    rw [hoff u (by omega)] at h1
    rw [hoff (u + 1) (by omega)] at h2
    rw [htgt t (by omega), htgt (t + 1) (by omega)]
    exact hsort u (by omega) t h1 h2
  · intro u v
    have hub : (u : ℕ) < G.vertices := u.isLt
    have hbound : offset g ((u : ℕ) + 1) ≤ 2 * ve x := hmono _ (by omega)
    rw [hg.adj_iff u v]
    constructor
    · rintro ⟨t, h1, h2, h3⟩
      exact ⟨t, by rw [hoff (u : ℕ) (by omega)]; exact h1,
        by rw [hoff ((u : ℕ) + 1) (by omega)]; exact h2,
        by rw [htgt t (by omega)]; exact h3⟩
    · rintro ⟨t, h1, h2, h3⟩
      rw [hoff (u : ℕ) (by omega)] at h1
      rw [hoff ((u : ℕ) + 1) (by omega)] at h2
      rw [htgt t (by omega)] at h3
      exact ⟨t, h1, h2, h3⟩

end Lax470956Proofs.Construction1Shape
