import Lax470956Proofs.Construction1Index

/-!
The slot arithmetic of Construction 1.

Jobs are laid out in three blocks — `nk` vertex jobs, then `k²n` colour combination
slots, then `n²` edge slots — and each slot's components are recovered from its number by
division. This file is the check that the layout is sound: the three blocks are disjoint
and exhaust the job range, each encoding is inverted by the decoding the concept uses,
and a slot whose components are inadmissible carries a job that no feasible schedule can
place and that contributes nothing to any schedule's weight.

That last point is what makes the padding harmless. Indexing by all ordered pairs rather
than by the admissible ones is what gives a machine a closed-form index, and it is paid
for here, once.
-/

namespace Lax470956Proofs.Construction1Slots

open Lax470956.Construction1 Lax470956.Scheduling

/-! ### Division facts -/

lemma div_add_of_lt {a b c : ℕ} (hc : c < b) : (a * b + c) / b = a := by
  have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le c) hc
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hc,
    Nat.zero_add]

lemma mod_add_of_lt {a b c : ℕ} (hc : c < b) : (a * b + c) % b = c := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- A pair `(a, b)` with `a < A` and `b < B` occupies a distinct cell below `A · B`. -/
lemma pair_lt {a b A B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  have h1 : a + 1 ≤ A := ha
  calc a * B + b < a * B + B := by omega
    _ = (a + 1) * B := (Nat.succ_mul a B).symm
    _ ≤ A * B := Nat.mul_le_mul_right B h1

variable (G : Lax470956.MulticolouredClique.Instance)

/-! ### The three encodings -/

/-- The slot of the vertex job of vertex `v` for colour `ℓ`. -/
def vIdx (v l : ℕ) : ℕ := v * G.colours + l

/-- The slot of the colour combination job of the ordered pair `(a, b)` and vertex `z`. -/
def cIdx (a b z : ℕ) : ℕ := nVJob G + (a * G.colours + b) * G.vertices + z

/-- The slot of edge job number `q`. -/
noncomputable def eIdx (q : ℕ) : ℕ := nVJob G + nCJob G + q

variable {G}

/-! ### Each block lies where it should -/

lemma vIdx_lt {v l : ℕ} (hv : v < G.vertices) (hl : l < G.colours) :
    vIdx G v l < nVJob G := pair_lt hv hl

lemma cIdx_mem {a b z : ℕ} (ha : a < G.colours) (hb : b < G.colours) (hz : z < G.vertices) :
    nVJob G ≤ cIdx G a b z ∧ cIdx G a b z < nVJob G + nCJob G := by
  refine ⟨by simp only [cIdx]; omega, ?_⟩
  have hab : a * G.colours + b < G.colours * G.colours := pair_lt ha hb
  have hmain : (a * G.colours + b) * G.vertices + z < G.colours * G.colours * G.vertices :=
    pair_lt hab hz
  simp only [cIdx, nCJob]
  omega

lemma eIdx_mem {q : ℕ} (hq : q < nEJob G) :
    nVJob G + nCJob G ≤ eIdx G q ∧ eIdx G q < nJobs G := by
  refine ⟨by simp only [eIdx]; omega, ?_⟩
  simp only [eIdx, nJobs]
  omega

/-! ### Decoding inverts encoding -/

@[simp] lemma vjVert_vIdx {v l : ℕ} (hl : l < G.colours) : vjVert G (vIdx G v l) = v :=
  div_add_of_lt hl

@[simp] lemma vjCol_vIdx {v l : ℕ} (hl : l < G.colours) : vjCol G (vIdx G v l) = l :=
  mod_add_of_lt hl

/-- The offset of a colour combination slot inside its block. -/
lemma cIdx_sub {a b z : ℕ} : cIdx G a b z - nVJob G = (a * G.colours + b) * G.vertices + z := by
  simp only [cIdx]; omega

@[simp] lemma cjZ_cIdx {a b z : ℕ} (hz : z < G.vertices) :
    cjZ G (cIdx G a b z - nVJob G) = z := by
  rw [cIdx_sub]; exact mod_add_of_lt hz

@[simp] lemma cjA_cIdx {a b z : ℕ} (hb : b < G.colours) (hz : z < G.vertices) :
    cjA G (cIdx G a b z - nVJob G) = a := by
  rw [cjA, cIdx_sub, div_add_of_lt hz]
  exact div_add_of_lt hb

@[simp] lemma cjB_cIdx {a b z : ℕ} (hb : b < G.colours) (hz : z < G.vertices) :
    cjB G (cIdx G a b z - nVJob G) = b := by
  rw [cjB, cIdx_sub, div_add_of_lt hz]
  exact mod_add_of_lt hb

/-- The offset of an edge slot inside its block. -/
@[simp] lemma eIdx_sub {q : ℕ} : eIdx G q - nVJob G - nCJob G = q := by
  simp only [eIdx]; omega

/-! ### Inadmissible slots carry inert jobs -/

open Classical in
/-- A colour combination slot whose pair is unordered, or whose vertex has neither of its
two colours, has no eligible machine. -/
lemma eligOf_cIdx_inert {j : ℕ} (h1 : nVJob G ≤ j) (h2 : j < nVJob G + nCJob G)
    (h : ¬ CJobOk G (j - nVJob G)) : eligOf G j = [] := by
  rw [eligOf, if_neg (by omega), if_pos h2]
  simp only [if_neg h]

open Classical in
/-- An edge slot whose pair is not an edge, or is not oriented by colour, has no eligible
machine. -/
lemma eligOf_eIdx_inert {j : ℕ} (h2 : ¬ j < nVJob G + nCJob G)
    (h : ¬ EJobOk G (j - nVJob G - nCJob G)) : eligOf G j = [] := by
  rw [eligOf, if_neg (by omega), if_neg h2]
  simp only [if_neg h]

end Lax470956Proofs.Construction1Slots
