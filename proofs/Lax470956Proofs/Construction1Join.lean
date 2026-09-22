import Lax470956Proofs.Construction1Typed
import Lax470956Proofs.Construction1Slots

/-!
Joining the paper's Construction 1 to the archive's.

The argument of Section 3 is proved in `Construction1Typed` over the paper's own shapes:
an abstract finite vertex type with a colouring and an edge relation, and jobs and
machines named structurally as sums and subtypes. The archive's shapes are numbered — a
graph on `Fin n`, and jobs and machines indexed by `Fin`. This file supplies the two
translations that let the one argument serve the other: the instance shape, and the
order `<π`, which the paper assumes and the concept defines.
-/

namespace Lax470956Proofs.Construction1Join

open Lax470956.Construction1 Lax470956.MulticolouredClique
open Lax470956Proofs.TypedIsem Lax470956Proofs.TypedMcc
open Lax470956Proofs.Construction1Typed.Construction1

variable (G : Lax470956.MulticolouredClique.Instance)

/-! ### The instance shape -/

/-- The paper's Multicoloured Clique instance, built from the archive's. -/
noncomputable def ofInstance : MCCInstance G.colours where
  V := Fin G.vertices
  fintypeV := inferInstance
  decEqV := inferInstance
  color := G.colour
  E := G.graph.Adj
  decE := Classical.decRel _
  E_symm := fun _ _ h => h.symm

lemma nG_ofInstance : nG (ofInstance G) = G.vertices := by
  simp only [nG, ofInstance]
  exact Fintype.card_fin _

/-- A multicoloured clique in one shape is a multicoloured clique in the other. -/
lemma hasClique_iff : (ofInstance G).HasClique ↔ G.HasMulticolouredClique := Iff.rfl

/-! ### The order `<π`

The concept ranks vertices by colour and breaks ties by index. That is the order induced
by the key `colour(v)·n + v`, and this section is the check that it is one of the orders
the paper's argument admits. -/

/-- The linear key the concept's rank counts below. -/
def key (v : Fin G.vertices) : ℕ := (G.colour v : ℕ) * G.vertices + (v : ℕ)

variable {G}

lemma key_lt_of_colour_lt {u v : Fin G.vertices}
    (h : (G.colour u : ℕ) < (G.colour v : ℕ)) : key G u < key G v := by
  have hu : (u : ℕ) < G.vertices := u.isLt
  have hstep : ((G.colour u : ℕ) + 1) * G.vertices ≤ (G.colour v : ℕ) * G.vertices :=
    Nat.mul_le_mul_right _ h
  rw [Nat.add_mul, Nat.one_mul] at hstep
  simp only [key]
  omega

lemma key_lt_iff {u v : Fin G.vertices} :
    key G u < key G v ↔
      ((G.colour u : ℕ) < (G.colour v : ℕ) ∨
        ((G.colour u : ℕ) = (G.colour v : ℕ) ∧ (u : ℕ) < (v : ℕ))) := by
  constructor
  · intro h
    rcases lt_trichotomy (G.colour u : ℕ) (G.colour v : ℕ) with hc | hc | hc
    · exact Or.inl hc
    · refine Or.inr ⟨hc, ?_⟩
      simp only [key, hc] at h
      omega
    · exact absurd h (by have := key_lt_of_colour_lt (G := G) hc; omega)
  · rintro (hc | ⟨hc, hlt⟩)
    · exact key_lt_of_colour_lt hc
    · simp only [key, hc]; omega

variable (G)

/-- The concept's rank counts the vertices strictly below `v` in the key order. -/
lemma filter_eq (v : Fin G.vertices) :
    (Finset.univ.filter fun u : Fin G.vertices =>
      ((G.colour u : ℕ) < (G.colour v : ℕ) ∨
        ((G.colour u : ℕ) = (G.colour v : ℕ) ∧ (u : ℕ) < (v : ℕ))))
      = Finset.univ.filter fun u : Fin G.vertices => key G u < key G v :=
  Finset.filter_congr fun u _ => (key_lt_iff (G := G) (u := u) (v := v)).symm

lemma rank_eq (v : Fin G.vertices) :
    rank G v = 1 + (Finset.univ.filter fun u : Fin G.vertices => key G u < key G v).card := by
  rw [rank, filter_eq]

variable {G}

lemma rank_lt_rank {u v : Fin G.vertices} (h : key G u < key G v) : rank G u < rank G v := by
  rw [rank_eq, rank_eq]
  have hcard : (Finset.univ.filter fun w : Fin G.vertices => key G w < key G u).card <
      (Finset.univ.filter fun w : Fin G.vertices => key G w < key G v).card := by
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact lt_trans hw h
    · intro hsub
      have hu : u ∈ Finset.univ.filter fun w : Fin G.vertices => key G w < key G v := by
        simpa using h
      have hu' := hsub hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu'
      exact absurd hu' (lt_irrefl _)
  omega

lemma rank_le (v : Fin G.vertices) : rank G v ≤ G.vertices := by
  rw [rank_eq]
  have hsub : (Finset.univ.filter fun u : Fin G.vertices => key G u < key G v) ⊆
      Finset.univ.erase v := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    exact absurd hw (lt_irrefl _)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at hcard
  have hpos : 0 < G.vertices := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  omega

lemma rank_pos (v : Fin G.vertices) : 0 < rank G v := by rw [rank_eq]; omega

lemma rank_inj : Function.Injective (rank G) := by
  intro u v huv
  rcases lt_trichotomy (key G u) (key G v) with h | h | h
  · exact absurd huv (Nat.ne_of_lt (rank_lt_rank h))
  · refine Fin.ext ?_
    rcases lt_trichotomy (G.colour u : ℕ) (G.colour v : ℕ) with hcc | hcc | hcc
    · exact absurd (key_lt_of_colour_lt hcc) (by omega)
    · simp only [key, hcc] at h; omega
    · exact absurd (key_lt_of_colour_lt hcc) (by omega)
  · exact absurd huv.symm (Nat.ne_of_lt (rank_lt_rank h))

lemma rank_mono {u v : Fin G.vertices} (h : (G.colour u : ℕ) < (G.colour v : ℕ)) :
    rank G u < rank G v := rank_lt_rank (key_lt_of_colour_lt h)

variable (G)

/-- **The concept's order is one the paper's argument admits.** -/
noncomputable def ord : VertexOrder (ofInstance G) where
  π := rank G
  π_pos := rank_pos
  π_le := fun v => by rw [nG_ofInstance]; exact rank_le v
  π_inj := rank_inj
  π_mono := fun _ _ h => rank_mono h

/-! ### The threshold, and what is left

The weight constants and the threshold are the same numbers on both sides, once the
vertex count is identified. What remains between the paper's argument and the concept's
statement is exactly one equivalence: that renumbering the jobs and machines, and padding
with the inert slots, preserves the existence of a feasible schedule of a given weight. -/

lemma c1_eq : Lax470956Proofs.Construction1Typed.Construction1.c1 (ofInstance G)
    = Lax470956.Construction1.c1 G := by
  simp only [Lax470956Proofs.Construction1Typed.Construction1.c1,
    Lax470956.Construction1.c1, nG_ofInstance]

lemma c2_eq : Lax470956Proofs.Construction1Typed.Construction1.c2 (ofInstance G)
    = Lax470956.Construction1.c2 G := by
  simp only [Lax470956Proofs.Construction1Typed.Construction1.c2,
    Lax470956.Construction1.c2, nG_ofInstance, c1_eq]

lemma c3_eq : Lax470956Proofs.Construction1Typed.Construction1.c3 (ofInstance G)
    = Lax470956.Construction1.c3 G := by
  simp only [Lax470956Proofs.Construction1Typed.Construction1.c3,
    Lax470956.Construction1.c3, nG_ofInstance, c2_eq]

lemma targetWeight_eq :
    Lax470956Proofs.Construction1Typed.Construction1.targetWeight (ofInstance G)
      = Lax470956.Construction1.targetWeight G := by
  simp only [Lax470956Proofs.Construction1Typed.Construction1.targetWeight,
    Lax470956.Construction1.targetWeight, nG_ofInstance, c1_eq, c2_eq, c3_eq]

/-- **Construction 1 is correct, modulo the renumbering.** The paper's argument, joined
to the archive's shapes at every point but one: the equivalence `hrenum`, which says that
numbering the jobs and machines and padding with inert slots changes neither side. -/
theorem correct_of_renumbering
    (hrenum : ∀ W : ℕ,
      (Lax470956Proofs.Construction1Typed.Construction1.isem (ofInstance G) (ord G)).HasWeight W
        ↔ (Lax470956.Construction1.inst G).HasWeight W) :
    G.HasMulticolouredClique ↔
      (Lax470956.Construction1.inst G).HasWeight (Lax470956.Construction1.targetWeight G) := by
  rw [← hasClique_iff, ← targetWeight_eq, ← hrenum]
  exact Lax470956Proofs.Construction1Typed.Construction1.theorem1_correctness (ofInstance G) (ord G)

end Lax470956Proofs.Construction1Join
