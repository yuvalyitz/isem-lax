import Lax888481.MulticolouredClique

/-!
A word determines the Multicoloured Clique instance it encodes.

The word is a graph block, a colour per vertex, and the number of colours. None of the
three parts is delimited, so the claim is not immediate: what makes the split unique is
that the graph block declares its own length in its first two entries — three header and
offset entries, one offset per vertex, and two target entries per edge. So the number of
vertices and the number of edges are read off the whole word, the graph block is the
prefix of the length they determine, and everything after it is determined in turn.

Two instances with the same encoding therefore have the same vertices, the same colours,
the same edges and the same colouring, and one has a multicoloured clique exactly when
the other does. So the reduction of the first theorem can choose an instance
for its input word without the choice mattering.
-/

namespace Lax888481Proofs.MccTransfer

open Lax888481.MulticolouredClique Lax271696.GraphEncoding

private lemma getD_prefix {g r : List ℕ} {i : ℕ} (hi : i < g.length) :
    (g ++ r).getD i 0 = g.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

variable {x : List ℕ} {G G' : Instance}

/-- The graph block is three entries longer than its offsets and target array, so it is
at least three entries long. -/
private lemma three_le_length {g : List ℕ} {n : ℕ} {A : SimpleGraph (Fin n)}
    (h : EncodesGraph g n A) : 3 ≤ g.length := by
  rw [h.length_eq]; omega

/-- The graph block's length is read off the whole word. -/
private lemma block_length {g c : List ℕ} {n : ℕ} {A : SimpleGraph (Fin n)}
    (hx : x = g ++ c) (h : EncodesGraph g n A) :
    g.length = 3 + vertexCount x + 2 * edgeCount x := by
  have h3 := three_le_length h
  have hv : vertexCount x = n := by
    rw [hx, vertexCount, getD_prefix (by omega)]; exact h.vertexCount_eq
  have he : edgeCount x = edgeCount g := by
    rw [hx, edgeCount, edgeCount, getD_prefix (by omega)]
  rw [hv, he]; exact h.length_eq

/-- **The graph blocks of two encodings of one word agree**, and so do the vertex
counts. -/
theorem block_eq (h : EncodesInstance x G) (h' : EncodesInstance x G') :
    ∃ hv : G.vertices = G'.vertices,
      G.colours = G'.colours ∧
      (∀ u v : Fin G.vertices,
        G.graph.Adj u v ↔ G'.graph.Adj (Fin.cast hv u) (Fin.cast hv v)) ∧
      (∀ v : Fin G.vertices, (G.colour v : ℕ) = (G'.colour (Fin.cast hv v) : ℕ)) := by
  obtain ⟨g, hx, hg, hsort⟩ := h
  obtain ⟨g', hx', hg', -⟩ := h'
  -- the two graph blocks have the same length, hence are equal
  have hxa : x = g ++ ((List.ofFn fun v : Fin G.vertices => (G.colour v : ℕ))
      ++ [G.colours]) := by rw [hx, List.append_assoc]
  have hxa' : x = g' ++ ((List.ofFn fun v : Fin G'.vertices => (G'.colour v : ℕ))
      ++ [G'.colours]) := by rw [hx', List.append_assoc]
  have hlen : g.length = g'.length := by
    rw [block_length hxa hg, block_length hxa' hg']
  obtain ⟨houter, hk⟩ := List.append_inj' (hx.symm.trans hx') rfl
  obtain ⟨hgg, hcl⟩ := List.append_inj houter hlen
  subst hgg
  -- so the vertex counts agree
  have hv : G.vertices = G'.vertices := by
    rw [← hg.vertexCount_eq, hg'.vertexCount_eq]
  refine ⟨hv, by simpa using hk, fun u v => ?_, fun v => ?_⟩
  · rw [hg.adj_iff u v, hg'.adj_iff (Fin.cast hv u) (Fin.cast hv v)]
    rfl
  · have hlt : (v : ℕ) < G'.vertices := by rw [← hv]; exact v.isLt
    have hcast : Fin.cast hv v = (⟨(v : ℕ), hlt⟩ : Fin G'.vertices) := rfl
    rw [hcast]
    have := congrArg (fun l => l.getD (v : ℕ) 0) hcl
    simpa [List.getD_eq_getElem?_getD, v.isLt, hlt] using this

/-- **Having a multicoloured clique does not depend on which instance a word is read
as.** -/
theorem hasClique_congr (h : EncodesInstance x G) (h' : EncodesInstance x G') :
    G.HasMulticolouredClique ↔ G'.HasMulticolouredClique := by
  -- one direction, applied twice
  have key : ∀ (A B : Instance), EncodesInstance x A → EncodesInstance x B →
      A.HasMulticolouredClique → B.HasMulticolouredClique := by
    intro A B hA hB hclq
    obtain ⟨hv, hc, hadj, hcol⟩ := block_eq hA hB
    obtain ⟨f, hf, hadjf⟩ := hclq
    refine ⟨fun c => Fin.cast hv (f (Fin.cast hc.symm c)), fun c => ?_, fun c c' hne => ?_⟩
    · refine Fin.ext ?_
      have := (hcol (f (Fin.cast hc.symm c))).symm
      rw [hf (Fin.cast hc.symm c)] at this
      exact this
    · refine (hadj _ _).mp (hadjf _ _ fun hcon => hne (Fin.ext ?_))
      exact congrArg (Fin.val (n := A.colours)) hcon
  exact ⟨key G G' h h', key G' G h' h⟩

/-- **The parameter of an encoding is its number of colours**: the last entry of the
word. -/
theorem param_eq (h : EncodesInstance x G) : (x.getLast?.getD 0) = G.colours := by
  obtain ⟨g, hx, -, -⟩ := h
  subst hx
  simp

end Lax888481Proofs.MccTransfer
