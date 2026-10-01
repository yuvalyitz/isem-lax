import Lax470956Proofs.Construction1Renum
import Lax470956Proofs.Encoder

/-!
Construction 1's instance, written out as a word.

The layout is `Encoder`'s, so all that is left here is what is about this construction:
that every machine number it lists is a machine, which is where the colour-pair numbering
of `Construction1Index` is used again.
-/

namespace Lax470956Proofs.Construction1Emit

open Lax470956.Construction1 Lax470956.MulticolouredClique Lax470956.InstanceEncoding
open Lax470956Proofs.Construction1Index Lax470956Proofs.Construction1Slots
open Lax470956Proofs.Construction1Renum

variable (G : Lax470956.MulticolouredClique.Instance)

/-- Construction 1's accessors, as the encoder wants them. -/
noncomputable def blocks : Lax470956Proofs.Encoder.Blocks :=
  ⟨nJobs G, nMach G, procOf G, dueOf G, wtOf G, eligOf G⟩

/-! ### Every Machine Number the Construction Lists Is a Machine -/

lemma vjCol_lt {j : ℕ} (hj : j < nVJob G) : vjCol G j < G.colours := by
  have hk : 0 < G.colours := by
    by_contra hcon
    have hz : G.colours = 0 := by omega
    simp only [nVJob, hz, Nat.mul_zero] at hj
    omega
  exact Nat.mod_lt _ hk

lemma col_lt (u : ℕ) : col (G := G) u < G.colours ∨ G.colours = 0 := by
  rcases Nat.eq_zero_or_pos G.colours with h | h
  · exact Or.inr h
  · refine Or.inl ?_
    rcases Nat.lt_or_ge u G.vertices with hu | hu
    · rw [col_mk hu]; exact (G.colour _).isLt
    · rw [col, dif_neg (by omega)]; exact h

lemma elig_lt_v {j : ℕ} (hj : j < nVJob G) {v : ℕ} (hv : v ∈ eligOf G j) : v < nMach G := by
  have hck := vjCol_lt G hj
  have hcv : col (G := G) (vjVert G j) < G.colours := by
    rcases col_lt G (vjVert G j) with h | h
    · exact h
    · omega
  rw [eligOf, if_pos hj] at hv
  split at hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    simp only [nMach, validation]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · simp only [nMach, validation]; omega
    · rename_i hne
      have hmm : min (vjCol G j) (col (G := G) (vjVert G j))
          < max (vjCol G j) (col (G := G) (vjVert G j)) := by omega
      have hmk : max (vjCol G j) (col (G := G) (vjVert G j)) < G.colours := by omega
      exact Nat.lt_succ_of_lt (pairIdx_lt hmm hmk)

lemma elig_lt_c {j : ℕ} (h1 : nVJob G ≤ j) (h2 : j < nVJob G + nCJob G) {v : ℕ}
    (hv : v ∈ eligOf G j) : v < nMach G := by
  rw [eligOf, if_neg (by omega), if_pos h2] at hv
  by_cases hok : CJobOk G (j - nVJob G)
  · simp only [if_pos hok, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    exact Nat.lt_succ_of_lt (pairIdx_lt hok.1 hok.2.1)
  · simp only [if_neg hok, List.not_mem_nil] at hv

lemma edge_col_lt {q : ℕ} (hq : q < nEJob G) :
    col (G := G) (ejU G q) < col (G := G) (ejV G q) ∧ col (G := G) (ejV G q) < G.colours := by
  have hmem : (edgeList G)[q] ∈ edgeList G := List.getElem_mem hq
  obtain ⟨hlt, -⟩ := (mem_edgeList G _).mp hmem
  have hu : ejU G q = ((edgeList G)[q].1 : ℕ) := by
    rw [ejU, List.getElem?_eq_getElem hq]; rfl
  have hvv : ejV G q = ((edgeList G)[q].2 : ℕ) := by
    rw [ejV, List.getElem?_eq_getElem hq]; rfl
  have hcu : col (G := G) (ejU G q) = (G.colour (edgeList G)[q].1 : ℕ) := by
    rw [hu, col_mk ((edgeList G)[q].1).isLt]
  have hcv : col (G := G) (ejV G q) = (G.colour (edgeList G)[q].2 : ℕ) := by
    rw [hvv, col_mk ((edgeList G)[q].2).isLt]
  rw [hcu, hcv]
  exact ⟨hlt, (G.colour _).isLt⟩

lemma elig_lt_e {j : ℕ} (h1 : ¬ j < nVJob G + nCJob G) (h2 : j < nJobs G) {v : ℕ}
    (hv : v ∈ eligOf G j) : v < nMach G := by
  have hq : j - nVJob G - nCJob G < nEJob G := by simp only [nJobs] at h2; omega
  rw [eligOf, if_neg (by omega), if_neg h1] at hv
  simp only [if_pos (show EJobOk G (j - nVJob G - nCJob G) from hq), List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl
  obtain ⟨hlt, hck⟩ := edge_col_lt G hq
  exact Nat.lt_succ_of_lt (pairIdx_lt hlt hck)

/-- **Every machine the construction lists is one of its machines.** -/
lemma elig_lt {j : ℕ} (hj : j < nJobs G) {v : ℕ} (hv : v ∈ eligOf G j) : v < nMach G := by
  rcases Nat.lt_or_ge j (nVJob G) with h | h
  · exact elig_lt_v G h hv
  · rcases Nat.lt_or_ge j (nVJob G + nCJob G) with h2 | h2
    · exact elig_lt_c G h h2 hv
    · exact elig_lt_e G (by omega) hj hv

/-! ### The Encoding -/

theorem encodesInstance_emit :
    EncodesInstance (Lax470956Proofs.Encoder.emit (blocks G)) (inst G) :=
  Lax470956Proofs.Encoder.encodesInstance (blocks G) (inst G) rfl rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun j hj _ hv => elig_lt G hj hv)
    (fun j i => by
      constructor
      · intro h; exact (Finset.mem_filter.mp h).2
      · intro h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/--
---
conclusion: Lax470956.Construction1.emit_encodes
---
The layout is the archive's, discharged once and generically in `Encoder`: the two
counts, one entry per job for each of the processing times, deadlines and weights, the
`n + 1` offsets, and the eligibility lists run together. What is about this construction
is only that every machine number it lists is a machine — the validation machine is
`C(k,2)` and the edge selection machines are numbered below it by `pairIdx`, which
`Construction1Index` shows lands exactly in `[0, C(k,2))`.

The word is the instance followed by the threshold, as a decision instance is.
-/
theorem emit_encodes (G : Lax470956.MulticolouredClique.Instance) :
    EncodesDecisionInstance (emit G) (inst G) (targetWeight G) :=
  ⟨Lax470956Proofs.Encoder.emit (blocks G), rfl, encodesInstance_emit G⟩

end Lax470956Proofs.Construction1Emit
