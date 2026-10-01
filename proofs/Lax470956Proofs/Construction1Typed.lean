import Lax470956Proofs.TypedIsem
import Lax470956Proofs.TypedMcc

namespace Lax470956Proofs.Construction1Typed

open Lax470956Proofs.TypedIsem Lax470956Proofs.TypedMcc

/-!
# Multicolored Clique → Interval Scheduling on Eligible Machines

A formalization of the W[1]-hardness reduction of Hermelin–Itzhaki–Molter–Shabtay,
*"On the parameterized complexity of interval scheduling with eligible machine sets"*,
JCSS 144 (2024) 103533: Section 3, Construction 1, Observation 3, Lemmas 1–2, Theorem 1.

## What Is Implemented

* `ISEM` — Interval Scheduling on Eligible Machines (Section 2), with schedules,
  conflicts, feasibility and the weight objective.
* `MCCInstance` — Multicolored Clique on a `k`-partite graph.
* `Construction1.VertexOrder` — the paper's order `<π`.
* `Construction1.Job`, `Construction1.Machine` — the full job and machine families.
* `Construction1.jobP / jobD / jobW / jobElig` — every processing time, deadline,
  weight and eligible-machine set of Construction 1, with all well-formedness
  obligations (`0 < p`, `p ≤ d`) discharged.
* `Construction1.isem` — the constructed ISEM instance (no placeholders).
* `Construction1.card_machine` — `m = C(k,2) + 1`, the parameter bound that makes
  this a *parameterized* reduction.
* `Construction1.start_*` — the exact interval layout of every job family
  (this is the content of Figures 1 and 2).
* `Construction1.targetWeight` — the threshold `W` of Lemmas 1 and 2.

## Status

**Complete.** Observation 3, Lemma 1, Lemma 2 and Theorem 1 are all proved;
The correctness of the reduction is proved here, never assumed.

## Deviations from the Paper (all Deliberate, All Documented)

1. **Colors are 0-indexed.** The paper uses `V₁, …, V_k`, i.e. `ℓ ∈ {1,…,k}`; here
   `ℓ : Fin k`, i.e. `ℓ ∈ {0,…,k-1}`. This is a uniform shift and preserves every
   interval relation. It additionally removes a degeneracy: with 1-based colors the
   color-combination job of the `π`-first vertex for the pair `(1,k)` has processing
   time `(k+2)·1 - k - 2 = 0`, an empty interval that conflicts with nothing.

2. **Edge-job processing time carries a `- 1` correction.** The paper states
   `p(jₑ) = (k+2)(π(v) - π(u)) - ℓ + ℓ'` with `d(jₑ) = (k+2)π(v) - ℓ - 1`, which makes
   `jₑ` start at `(k+2)π(u) - ℓ' - 1` — exactly where the vertex job `j_u^{(ℓ')}` starts,
   so the two conflict and the schedule built in Lemma 1 is infeasible. Figure 1 shows
   `jₑ` starting *after* `j_u^{(ℓ')}` ends, i.e. at `(k+2)π(u) - ℓ'`, which forces
   `p(jₑ) = (k+2)(π(v) - π(u)) - ℓ + ℓ' - 1`. That is what is formalized here; see
   `Construction1.start_edge`.

3. **Index types instead of `Fin n`.** Jobs and machines are `Fintype`s rather than
   `Fin n` / `Fin m`, so the construction is definable without an ad-hoc enumeration.
   Machines are `Option (ColorPair k)`, with `none` the validation machine;
   `Construction1.card_machine` recovers the paper's count `C(k,2) + 1`.
-/

open scoped BigOperators

/-! ## 3. Construction 1 -/

namespace Construction1

/-- An (unordered) color combination `ℓ < ℓ'`, i.e. one edge selection machine. -/
abbrev ColorPair (k : ℕ) : Type := {c : Fin k × Fin k // c.1 < c.2}

namespace ColorPair

variable {k : ℕ}

/-- The smaller color `ℓ` of the combination. -/
def lo (c : ColorPair k) : Fin k := c.1.1

/-- The larger color `ℓ'` of the combination. -/
def hi (c : ColorPair k) : Fin k := c.1.2

lemma lo_lt_hi (c : ColorPair k) : c.lo < c.hi := c.2

lemma lo_ne_hi (c : ColorPair k) : c.lo ≠ c.hi := ne_of_lt c.lo_lt_hi

lemma eq_of {c c' : ColorPair k} (h1 : c.lo = c'.lo) (h2 : c.hi = c'.hi) : c = c' := by
  obtain ⟨⟨a, b⟩, hab⟩ := c
  obtain ⟨⟨a', b'⟩, hab'⟩ := c'
  simp only [lo, hi] at h1 h2
  subst h1; subst h2; rfl

end ColorPair

/-- `{(a,b) : Fin k × Fin k // a < b} ≃ Σ b, {a // a < b}`. -/
private def colorPairEquiv (k : ℕ) : ColorPair k ≃ Σ b : Fin k, {a : Fin k // a < b} where
  toFun c := ⟨c.1.2, ⟨c.1.1, c.2⟩⟩
  invFun x := ⟨(x.2.1, x.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def finLtEquiv {k : ℕ} (b : Fin k) : {a : Fin k // a < b} ≃ Fin b.val where
  toFun a := ⟨a.1.val, a.2⟩
  invFun i := ⟨⟨i.1, lt_trans i.2 b.isLt⟩, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The paper's machine count: there are exactly `C(k,2)` color combinations. -/
theorem card_colorPair (k : ℕ) : Fintype.card (ColorPair k) = Nat.choose k 2 := by
  have h1 : Fintype.card (ColorPair k) = ∑ b : Fin k, (b : ℕ) := by
    rw [Fintype.card_congr (colorPairEquiv k), Fintype.card_sigma]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Fintype.card_congr (finLtEquiv b), Fintype.card_fin]
  have h2 : (∑ b : Fin k, (b : ℕ)) = ∑ i ∈ Finset.range k, i :=
    Fin.sum_univ_eq_sum_range (fun i => i) k
  have h3 := Finset.sum_range_id_mul_two k
  rw [h1, h2, Nat.choose_two_right]
  omega

variable {k : ℕ} (G : MCCInstance k)

/-- `n_G`, the number of vertices of the Multicolored Clique instance. -/
def nG : ℕ := Fintype.card G.V

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The paper's total order `<π` on `V`, presented by its ordinal-position function.
`π` enumerates `V` as `1, …, n_G` and refines the color order. -/
structure VertexOrder where
  π : G.V → ℕ
  π_pos : ∀ v, 0 < π v
  π_le : ∀ v, π v ≤ nG G
  π_inj : Function.Injective π
  π_mono : ∀ u v, G.color u < G.color v → π u < π v

/-! ### 3.1 Weight Constants -/

/-- `c₁ = n_G + 1`. -/
def c1 : ℕ := nG G + 1

/-- `c₂ = (k-1)·n_G·c₁ + n_G + 1`. -/
def c2 : ℕ := (k - 1) * nG G * c1 G + nG G + 1

/-- `c₃ = (k·n_G + k²·n_G)·n_G·c₂ + 1`. -/
def c3 : ℕ := (k * nG G + k ^ 2 * nG G) * nG G * c2 G + 1

/-! ### 3.2 Jobs and Machines -/

/-- A vertex job `j_v^{(ℓ)}`: a vertex together with one of the `k` colors. -/
abbrev VJob : Type := G.V × Fin k

/-- An edge job `j_e`: an edge `{u,v} ∈ E` oriented so that `color u < color v`. -/
abbrev EJob : Type := {e : G.V × G.V // G.color e.1 < G.color e.2 ∧ G.E e.1 e.2}

/-- A color-combination job `j_z^{(ℓ,ℓ')}`: a color combination `ℓ < ℓ'` together with
a vertex `z` of color `ℓ` or `ℓ'`. -/
abbrev CJob : Type := {x : ColorPair k × G.V // G.color x.2 = x.1.lo ∨ G.color x.2 = x.1.hi}

-- These two are found by `inferInstance` on their own, but registering them keeps
-- instance search for the `Sum` below in reach.
instance : DecidableEq (EJob G) := Subtype.instDecidableEq
instance : DecidableEq (CJob G) := Subtype.instDecidableEq

/-- All jobs of Construction 1: vertex jobs, edge jobs, color-combination jobs. -/
abbrev Job : Type := VJob G ⊕ EJob G ⊕ CJob G

/-- Machines: one *edge selection machine* per color combination, plus the single
*validation machine* `none`. -/
abbrev Machine (k : ℕ) : Type := Option (ColorPair k)

/-- The validation machine `i_{C(k,2)+1}`. -/
def validationMachine (k : ℕ) : Machine k := none

/-- The edge selection machine of color combination `c`. -/
def edgeMachine {k : ℕ} (c : ColorPair k) : Machine k := some c

lemma edgeMachine_ne_validation (c : ColorPair k) :
    edgeMachine c ≠ validationMachine k := by
  simp [edgeMachine, validationMachine]

lemma edgeMachine_inj {c c' : ColorPair k} (h : edgeMachine c = edgeMachine c') : c = c' := by
  simpa [edgeMachine] using h

/-- `m = C(k,2) + 1`, exactly as in the paper. -/
theorem card_machine (k : ℕ) : Fintype.card (Machine k) = Nat.choose k 2 + 1 := by
  rw [Fintype.card_option, card_colorPair]

/-! ### 3.3 Processing times, deadlines and weights

Throughout `K := k + 2`, and colors are used via their `ℕ`-values (`0`-indexed; see
the deviation note in the module docstring). -/

variable (ord : VertexOrder G)

/-- Processing time of `j_v^{(ℓ)}`: `k+2` for the vertex's own color, `1` otherwise. -/
def vP (x : VJob G) : ℕ := if x.2 = G.color x.1 then k + 2 else 1

/-- Deadline of `j_v^{(ℓ)}`: `(k+2)π(v) + 1` for the own color, `(k+2)π(v) - ℓ` otherwise. -/
def vD (x : VJob G) : ℕ :=
  if x.2 = G.color x.1 then (k + 2) * ord.π x.1 + 1 else (k + 2) * ord.π x.1 - (x.2 : ℕ)

/-- Weight of `j_v^{(ℓ)}`: `1` for the own color, `c₁` otherwise. -/
def vW (x : VJob G) : ℕ := if x.2 = G.color x.1 then 1 else c1 G

@[simp] lemma vP_own (v : G.V) : vP G (v, G.color v) = k + 2 := if_pos rfl
@[simp] lemma vD_own (v : G.V) : vD G ord (v, G.color v) = (k + 2) * ord.π v + 1 := if_pos rfl
@[simp] lemma vW_own (v : G.V) : vW G (v, G.color v) = 1 := if_pos rfl

lemma vP_other {v : G.V} {ℓ : Fin k} (h : ℓ ≠ G.color v) : vP G (v, ℓ) = 1 := if_neg h
lemma vD_other {v : G.V} {ℓ : Fin k} (h : ℓ ≠ G.color v) :
    vD G ord (v, ℓ) = (k + 2) * ord.π v - (ℓ : ℕ) := if_neg h
lemma vW_other {v : G.V} {ℓ : Fin k} (h : ℓ ≠ G.color v) : vW G (v, ℓ) = c1 G := if_neg h

/-- Processing time of `jₑ` for `e = {u,v}`, `u ∈ V_ℓ`, `v ∈ V_{ℓ'}`, `ℓ < ℓ'`:
`(k+2)(π(v) - π(u)) - ℓ + ℓ' - 1`. (The trailing `- 1` corrects the paper; see the
module docstring and `start_edge`.) -/
def eP (e : EJob G) : ℕ :=
  (k + 2) * (ord.π e.1.2 - ord.π e.1.1) - (G.color e.1.1 : ℕ) + (G.color e.1.2 : ℕ) - 1

/-- Deadline of `jₑ`: `(k+2)π(v) - ℓ - 1`. -/
def eD (e : EJob G) : ℕ := (k + 2) * ord.π e.1.2 - (G.color e.1.1 : ℕ) - 1

/-- Weight of `jₑ`: `c₂(π(v) - π(u)) + c₃`. -/
def eW (e : EJob G) : ℕ := c2 G * (ord.π e.1.2 - ord.π e.1.1) + c3 G

/-- Processing time of `j_z^{(ℓ,ℓ')}`: `(k+2)π(z) - ℓ' - 2` if `z ∈ V_ℓ`, and
`(k+2)(n_G - π(z)) + ℓ + 2` if `z ∈ V_{ℓ'}`. -/
def cP (x : CJob G) : ℕ :=
  if G.color x.1.2 = x.1.1.lo then (k + 2) * ord.π x.1.2 - (x.1.1.hi : ℕ) - 2
  else (k + 2) * (nG G - ord.π x.1.2) + (x.1.1.lo : ℕ) + 2

/-- Deadline of `j_z^{(ℓ,ℓ')}`: `(k+2)π(z) - ℓ' - 1` if `z ∈ V_ℓ`, and `(k+2)n_G + 2`
if `z ∈ V_{ℓ'}`. -/
def cD (x : CJob G) : ℕ :=
  if G.color x.1.2 = x.1.1.lo then (k + 2) * ord.π x.1.2 - (x.1.1.hi : ℕ) - 1
  else (k + 2) * nG G + 2

/-- Weight of `j_z^{(ℓ,ℓ')}`: `c₂·π(z)` if `z ∈ V_ℓ`, and `c₂(n_G - π(z))` if `z ∈ V_{ℓ'}`. -/
def cW (x : CJob G) : ℕ :=
  if G.color x.1.2 = x.1.1.lo then c2 G * ord.π x.1.2 else c2 G * (nG G - ord.π x.1.2)

lemma cP_lo (x : CJob G) (h : G.color x.1.2 = x.1.1.lo) :
    cP G ord x = (k + 2) * ord.π x.1.2 - (x.1.1.hi : ℕ) - 2 := if_pos h
lemma cP_hi (x : CJob G) (h : ¬ G.color x.1.2 = x.1.1.lo) :
    cP G ord x = (k + 2) * (nG G - ord.π x.1.2) + (x.1.1.lo : ℕ) + 2 := if_neg h
lemma cD_lo (x : CJob G) (h : G.color x.1.2 = x.1.1.lo) :
    cD G ord x = (k + 2) * ord.π x.1.2 - (x.1.1.hi : ℕ) - 1 := if_pos h
lemma cD_hi (x : CJob G) (h : ¬ G.color x.1.2 = x.1.1.lo) :
    cD G ord x = (k + 2) * nG G + 2 := if_neg h
lemma cW_lo (x : CJob G) (h : G.color x.1.2 = x.1.1.lo) :
    cW G ord x = c2 G * ord.π x.1.2 := if_pos h
lemma cW_hi (x : CJob G) (h : ¬ G.color x.1.2 = x.1.1.lo) :
    cW G ord x = c2 G * (nG G - ord.π x.1.2) := if_neg h

/-- Processing time of an arbitrary job. -/
def jobP : Job G → ℕ
  | Sum.inl x => vP G x
  | Sum.inr (Sum.inl e) => eP G ord e
  | Sum.inr (Sum.inr x) => cP G ord x

/-- Deadline of an arbitrary job. -/
def jobD : Job G → ℕ
  | Sum.inl x => vD G ord x
  | Sum.inr (Sum.inl e) => eD G ord e
  | Sum.inr (Sum.inr x) => cD G ord x

/-- Weight of an arbitrary job. -/
def jobW : Job G → ℕ
  | Sum.inl x => vW G x
  | Sum.inr (Sum.inl e) => eW G ord e
  | Sum.inr (Sum.inr x) => cW G ord x

@[simp] def jobP_vertex (x : VJob G) : jobP G ord (Sum.inl x) = vP G x := rfl
@[simp] def jobP_edge (e : EJob G) : jobP G ord (Sum.inr (Sum.inl e)) = eP G ord e := rfl
@[simp] def jobP_comb (x : CJob G) : jobP G ord (Sum.inr (Sum.inr x)) = cP G ord x := rfl
@[simp] def jobD_vertex (x : VJob G) : jobD G ord (Sum.inl x) = vD G ord x := rfl
@[simp] def jobD_edge (e : EJob G) : jobD G ord (Sum.inr (Sum.inl e)) = eD G ord e := rfl
@[simp] def jobD_comb (x : CJob G) : jobD G ord (Sum.inr (Sum.inr x)) = cD G ord x := rfl
@[simp] def jobW_vertex (x : VJob G) : jobW G ord (Sum.inl x) = vW G x := rfl
@[simp] def jobW_edge (e : EJob G) : jobW G ord (Sum.inr (Sum.inl e)) = eW G ord e := rfl
@[simp] def jobW_comb (x : CJob G) : jobW G ord (Sum.inr (Sum.inr x)) = cW G ord x := rfl

/-! ### 3.4 Eligible Machine Sets -/

/-- Eligible machines of `j_v^{(ℓ)}`: always the validation machine, plus the edge
selection machine of the combination `{color v, ℓ}` when `ℓ ≠ color v`. -/
def vElig (x : VJob G) : Finset (Machine k) :=
  insert (validationMachine k)
    ((Finset.univ.filter fun c : ColorPair k =>
        (G.color x.1 = c.lo ∧ x.2 = c.hi) ∨ (G.color x.1 = c.hi ∧ x.2 = c.lo)).image
      edgeMachine)

/-- Eligible machines of `jₑ`: the single edge selection machine of `{color u, color v}`. -/
def eElig (e : EJob G) : Finset (Machine k) :=
  {edgeMachine (⟨(G.color e.1.1, G.color e.1.2), e.2.1⟩ : ColorPair k)}

/-- Eligible machines of `j_z^{(ℓ,ℓ')}`: the single edge selection machine of `{ℓ,ℓ'}`. -/
def cElig (x : CJob G) : Finset (Machine k) := {edgeMachine x.1.1}

/-- Eligible machines of an arbitrary job. -/
def jobElig : Job G → Finset (Machine k)
  | Sum.inl x => vElig G x
  | Sum.inr (Sum.inl e) => eElig G e
  | Sum.inr (Sum.inr x) => cElig G x

lemma validation_mem_vElig (x : VJob G) : validationMachine k ∈ vElig G x :=
  Finset.mem_insert_self _ _

lemma mem_vElig_edge (x : VJob G) (c : ColorPair k) :
    edgeMachine c ∈ vElig G x ↔
      (G.color x.1 = c.lo ∧ x.2 = c.hi) ∨ (G.color x.1 = c.hi ∧ x.2 = c.lo) := by
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact absurd h (edgeMachine_ne_validation c)
    · obtain ⟨c', hc', hc''⟩ := Finset.mem_image.mp h
      have hcc : c' = c := edgeMachine_inj hc''
      subst hcc
      simpa using hc'
  · intro h
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c, by simpa using h, rfl⟩)

/-- The own-color vertex job is eligible *only* on the validation machine (Figure 2). -/
lemma vElig_ownColor (v : G.V) : vElig G (v, G.color v) = {validationMachine k} := by
  ext i
  cases i with
  | none =>
    simp only [validationMachine, Finset.mem_singleton, iff_true]
    exact Finset.mem_insert_self _ _
  | some c =>
    have hnot : ¬ (edgeMachine c ∈ vElig G (v, G.color v)) := by
      rw [mem_vElig_edge]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact c.lo_ne_hi (h1.symm.trans h2)
      · exact c.lo_ne_hi (h2.symm.trans h1)
    simp only [validationMachine, Finset.mem_singleton, reduceCtorEq, iff_false]
    exact hnot

/-! ### 3.5 Well-Formedness of the Construction -/

section Arithmetic

variable {G ord}

private lemma K_le_Kpi (v : G.V) : k + 2 ≤ (k + 2) * ord.π v := by
  have h : 1 ≤ ord.π v := ord.π_pos v
  calc k + 2 = (k + 2) * 1 := (Nat.mul_one _).symm
    _ ≤ (k + 2) * ord.π v := Nat.mul_le_mul le_rfl h

private lemma Kpi_le_KnG (v : G.V) : (k + 2) * ord.π v ≤ (k + 2) * nG G :=
  Nat.mul_le_mul le_rfl (ord.π_le v)

private lemma KnGsub_add_K_le (v : G.V) :
    (k + 2) * (nG G - ord.π v) + (k + 2) ≤ (k + 2) * nG G := by
  have h1 : 1 ≤ ord.π v := ord.π_pos v
  have h2 : ord.π v ≤ nG G := ord.π_le v
  have h3 : (nG G - ord.π v) + 1 ≤ nG G := by omega
  calc (k + 2) * (nG G - ord.π v) + (k + 2)
      = (k + 2) * ((nG G - ord.π v) + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ (k + 2) * nG G := Nat.mul_le_mul le_rfl h3

/-- `(k+2)·π(z) + (k+2)·(n_G - π(z)) = (k+2)·n_G`. -/
private lemma Kpi_add_KnGsub (v : G.V) :
    (k + 2) * ord.π v + (k + 2) * (nG G - ord.π v) = (k + 2) * nG G := by
  have h2 : ord.π v ≤ nG G := ord.π_le v
  rw [← Nat.mul_add]
  congr 1
  omega

private lemma K_le_Kdiff {u v : G.V} (h : ord.π u < ord.π v) :
    k + 2 ≤ (k + 2) * (ord.π v - ord.π u) := by
  have h1 : 1 ≤ ord.π v - ord.π u := by omega
  calc k + 2 = (k + 2) * 1 := (Nat.mul_one _).symm
    _ ≤ (k + 2) * (ord.π v - ord.π u) := Nat.mul_le_mul le_rfl h1

private lemma Kdiff_add_K_le_Kpi {u v : G.V} (h : ord.π u < ord.π v) :
    (k + 2) * (ord.π v - ord.π u) + (k + 2) ≤ (k + 2) * ord.π v := by
  have h1 : 1 ≤ ord.π u := ord.π_pos u
  have h2 : (ord.π v - ord.π u) + 1 ≤ ord.π v := by omega
  calc (k + 2) * (ord.π v - ord.π u) + (k + 2)
      = (k + 2) * ((ord.π v - ord.π u) + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ (k + 2) * ord.π v := Nat.mul_le_mul le_rfl h2

/-- `(k+2)·π(u) + (k+2)·(π(v) - π(u)) = (k+2)·π(v)`. -/
private lemma Kpiu_add_Kdiff {u v : G.V} (h : ord.π u < ord.π v) :
    (k + 2) * ord.π u + (k + 2) * (ord.π v - ord.π u) = (k + 2) * ord.π v := by
  rw [← Nat.mul_add]
  congr 1
  omega

end Arithmetic

variable {G ord}

lemma vP_pos (x : VJob G) : 0 < vP G x := by
  simp only [vP]; split <;> omega

lemma vP_le_vD (x : VJob G) : vP G x ≤ vD G ord x := by
  have hK := K_le_Kpi (ord := ord) x.1
  have hc : (x.2 : ℕ) < k := x.2.isLt
  simp only [vP, vD]
  split <;> omega

lemma eP_pos (e : EJob G) : 0 < eP G ord e := by
  have hlt : ord.π e.1.1 < ord.π e.1.2 := ord.π_mono _ _ e.2.1
  have hK := K_le_Kdiff (ord := ord) hlt
  have hc : (G.color e.1.1 : ℕ) < k := (G.color e.1.1).isLt
  have hc' : (G.color e.1.1 : ℕ) < (G.color e.1.2 : ℕ) := e.2.1
  simp only [eP]
  omega

lemma eP_le_eD (e : EJob G) : eP G ord e ≤ eD G ord e := by
  have hlt : ord.π e.1.1 < ord.π e.1.2 := ord.π_mono _ _ e.2.1
  have h1 := K_le_Kdiff (ord := ord) hlt
  have h2 := Kdiff_add_K_le_Kpi (ord := ord) hlt
  have hc : (G.color e.1.2 : ℕ) < k := (G.color e.1.2).isLt
  have hc' : (G.color e.1.1 : ℕ) < (G.color e.1.2 : ℕ) := e.2.1
  simp only [eP, eD]
  omega

lemma cP_pos (x : CJob G) : 0 < cP G ord x := by
  have hK := K_le_Kpi (ord := ord) x.1.2
  have hlo : (x.1.1.lo : ℕ) < k := x.1.1.lo.isLt
  have hhi : (x.1.1.hi : ℕ) < k := x.1.1.hi.isLt
  simp only [cP]
  split <;> omega

lemma cP_le_cD (x : CJob G) : cP G ord x ≤ cD G ord x := by
  have hK := K_le_Kpi (ord := ord) x.1.2
  have hn := KnGsub_add_K_le (ord := ord) x.1.2
  have hlo : (x.1.1.lo : ℕ) < k := x.1.1.lo.isLt
  have hhi : (x.1.1.hi : ℕ) < k := x.1.1.hi.isLt
  simp only [cP, cD]
  split <;> omega

theorem jobP_pos (j : Job G) : 0 < jobP G ord j := by
  cases j with
  | inl x => exact vP_pos x
  | inr y => cases y with
    | inl e => exact eP_pos e
    | inr x => exact cP_pos x

theorem jobP_le_jobD (j : Job G) : jobP G ord j ≤ jobD G ord j := by
  cases j with
  | inl x => exact vP_le_vD x
  | inr y => cases y with
    | inl e => exact eP_le_eD e
    | inr x => exact cP_le_cD x

variable (G ord)

/-- **Construction 1.** The Interval Scheduling on Eligible Machines instance built
from the Multicolored Clique instance `G` and the vertex order `ord`. -/
def isem : ISEM where
  Job := Job G
  Machine := Machine k
  jobFintype := inferInstanceAs (Fintype (VJob G ⊕ EJob G ⊕ CJob G))
  jobDecEq := inferInstanceAs (DecidableEq (VJob G ⊕ EJob G ⊕ CJob G))
  machineFintype := inferInstanceAs (Fintype (Option (ColorPair k)))
  machineDecEq := inferInstanceAs (DecidableEq (Option (ColorPair k)))
  p := jobP G ord
  d := jobD G ord
  w := jobW G ord
  elig := jobElig G
  p_pos := jobP_pos
  p_le_d := jobP_le_jobD

@[simp] def isem_p : (isem G ord).p = jobP G ord := rfl
@[simp] def isem_d : (isem G ord).d = jobD G ord := rfl
@[simp] def isem_w : (isem G ord).w = jobW G ord := rfl
@[simp] def isem_elig : (isem G ord).elig = jobElig G := rfl

/-! ### 3.6 The interval layout (Figures 1 and 2)

These lemmas pin down the start point `d j - p j` of every job family; together with
the deadlines they are exactly what Figures 1 and 2 depict, and they are the arithmetic
input to Lemmas 1 and 2. -/

variable {G ord}

/-- The own-color vertex job of `v` spans `[(k+2)π(v) - (k+1), (k+2)π(v) + 1)`. -/
lemma start_vertex_own (v : G.V) :
    (isem G ord).start (Sum.inl (v, G.color v)) = (k + 2) * ord.π v - (k + 1) := by
  have hK := K_le_Kpi (ord := ord) v
  change vD G ord (v, G.color v) - vP G (v, G.color v) = _
  rw [vD_own, vP_own]
  omega

/-- A non-own-color vertex job `j_v^{(ℓ)}` spans the unit interval
`[(k+2)π(v) - ℓ - 1, (k+2)π(v) - ℓ)`. -/
lemma start_vertex_other {v : G.V} {ℓ : Fin k} (h : ℓ ≠ G.color v) :
    (isem G ord).start (Sum.inl (v, ℓ)) = (k + 2) * ord.π v - (ℓ : ℕ) - 1 := by
  change vD G ord (v, ℓ) - vP G (v, ℓ) = _
  rw [vD_other G ord h, vP_other G h]

/-- **The corrected edge job.** `jₑ` spans `[(k+2)π(u) - ℓ', (k+2)π(v) - ℓ - 1)`:
it starts exactly at the deadline of `j_u^{(ℓ')}` and ends exactly at the start of
`j_v^{(ℓ)}`, as drawn in Figure 1. -/
lemma start_edge (e : EJob G) :
    (isem G ord).start (Sum.inr (Sum.inl e)) =
      (k + 2) * ord.π e.1.1 - (G.color e.1.2 : ℕ) := by
  have hlt : ord.π e.1.1 < ord.π e.1.2 := ord.π_mono _ _ e.2.1
  have h1 := K_le_Kdiff (ord := ord) hlt
  have h2 := Kdiff_add_K_le_Kpi (ord := ord) hlt
  have h3 := K_le_Kpi (ord := ord) e.1.1
  have h4 := Kpiu_add_Kdiff (ord := ord) hlt
  have hc : (G.color e.1.2 : ℕ) < k := (G.color e.1.2).isLt
  have hc' : (G.color e.1.1 : ℕ) < (G.color e.1.2 : ℕ) := e.2.1
  change eD G ord e - eP G ord e = _
  simp only [eD, eP]
  omega

/-- The `V_ℓ`-side color-combination job spans `[1, (k+2)π(z) - ℓ' - 1)`. -/
lemma start_comb_lo (x : CJob G) (h : G.color x.1.2 = x.1.1.lo) :
    (isem G ord).start (Sum.inr (Sum.inr x)) = 1 := by
  have hK := K_le_Kpi (ord := ord) x.1.2
  have hhi : (x.1.1.hi : ℕ) < k := x.1.1.hi.isLt
  change cD G ord x - cP G ord x = _
  rw [cD_lo G ord x h, cP_lo G ord x h]
  omega

/-- The `V_{ℓ'}`-side color-combination job spans `[(k+2)π(z) - ℓ, (k+2)n_G + 2)`. -/
lemma start_comb_hi (x : CJob G) (h : ¬ G.color x.1.2 = x.1.1.lo) :
    (isem G ord).start (Sum.inr (Sum.inr x)) = (k + 2) * ord.π x.1.2 - (x.1.1.lo : ℕ) := by
  have hK := K_le_Kpi (ord := ord) x.1.2
  have hle := Kpi_le_KnG (ord := ord) x.1.2
  have hsum := Kpi_add_KnGsub (ord := ord) x.1.2
  have hlo : (x.1.1.lo : ℕ) < k := x.1.1.lo.isLt
  change cD G ord x - cP G ord x = _
  rw [cD_hi G ord x h, cP_hi G ord x h]
  omega

/-- **Figure 1, verified.** Fix a color combination `{ℓ, ℓ'}` given by an edge
`e = {u,v}` with `color u = ℓ < ℓ' = color v`. The five jobs that Lemma 1 places on the
corresponding edge selection machine — `j_u^{(ℓ,ℓ')}`, `j_u^{(ℓ')}`, `jₑ`, `j_v^{(ℓ)}`,
`j_v^{(ℓ,ℓ')}` — occupy *consecutive* intervals: each one's deadline is exactly the
next one's start point. With `p_le_d` this makes all five pairwise non-conflicting
(via `ISEM.not_conflict_of_le`), as feasibility in Lemma 1 requires.

This is the fact that fails for the processing time printed in the paper: there `jₑ`
would start at `(k+2)π(u) - ℓ' - 1`, one unit *before* `j_u^{(ℓ')}` ends. -/
theorem edgeMachine_layout {c : ColorPair k} {u v : G.V}
    (hu : G.color u = c.lo) (hv : G.color v = c.hi)
    (hlt : G.color u < G.color v) (he : G.E u v) :
    (isem G ord).d (Sum.inr (Sum.inr ⟨(c, u), Or.inl hu⟩))
        ≤ (isem G ord).start (Sum.inl (u, c.hi))
    ∧ (isem G ord).d (Sum.inl (u, c.hi))
        ≤ (isem G ord).start (Sum.inr (Sum.inl ⟨(u, v), hlt, he⟩))
    ∧ (isem G ord).d (Sum.inr (Sum.inl ⟨(u, v), hlt, he⟩))
        ≤ (isem G ord).start (Sum.inl (v, c.lo))
    ∧ (isem G ord).d (Sum.inl (v, c.lo))
        ≤ (isem G ord).start (Sum.inr (Sum.inr ⟨(c, v), Or.inr hv⟩)) := by
  have hlohi : c.lo ≠ c.hi := c.lo_ne_hi
  have hne1 : c.hi ≠ G.color u := by rw [hu]; exact hlohi.symm
  have hne2 : c.lo ≠ G.color v := by rw [hv]; exact hlohi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [start_vertex_other hne1]
    change cD G ord _ ≤ _
    rw [cD_lo G ord _ hu]
  · rw [start_edge]
    change vD G ord _ ≤ _
    rw [vD_other G ord hne1]
    dsimp only
    rw [hv]
  · rw [start_vertex_other hne2]
    change eD G ord _ ≤ _
    simp only [eD]
    rw [hu]
  · rw [start_comb_hi _ (by dsimp only; rw [hv]; exact hlohi.symm)]
    change vD G ord _ ≤ _
    rw [vD_other G ord hne2]

/-- Every vertex job of `v` ends by `(k+2)π(v) + 1`. -/
lemma vD_le_bound (x : VJob G) : vD G ord x ≤ (k + 2) * ord.π x.1 + 1 := by
  simp only [vD]
  split <;> omega

/-- Every vertex job of `v` starts at or after `(k+2)π(v) - (k+1)`. -/
lemma le_start_vertex (x : VJob G) :
    (k + 2) * ord.π x.1 - (k + 1) ≤ (isem G ord).start (Sum.inl x) := by
  obtain ⟨v, ℓ⟩ := x
  by_cases h : ℓ = G.color v
  · subst h
    rw [start_vertex_own]
  · rw [start_vertex_other h]
    have hc : (ℓ : ℕ) < k := ℓ.isLt
    dsimp only
    omega

/-- **Figure 2, verified.** All `k` vertex jobs of a vertex `v` live inside
`[(k+2)π(v) - (k+1), (k+2)π(v) + 1)`, so vertex jobs of `π`-distinct vertices are
separated no matter which colors they carry. -/
lemma vertex_sep_of_π_lt {v v' : G.V} (ℓ ℓ' : Fin k) (h : ord.π v < ord.π v') :
    (isem G ord).d (Sum.inl (v, ℓ)) ≤ (isem G ord).start (Sum.inl (v', ℓ')) := by
  have hstep : (k + 2) * ord.π v + (k + 2) ≤ (k + 2) * ord.π v' := by
    have h1 : ord.π v + 1 ≤ ord.π v' := h
    calc (k + 2) * ord.π v + (k + 2) = (k + 2) * (ord.π v + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
      _ ≤ (k + 2) * ord.π v' := Nat.mul_le_mul le_rfl h1
  have hd : (isem G ord).d (Sum.inl (v, ℓ)) ≤ (k + 2) * ord.π v + 1 := vD_le_bound (v, ℓ)
  have hs : (k + 2) * ord.π v' - (k + 1) ≤ (isem G ord).start (Sum.inl (v', ℓ')) :=
    le_start_vertex (v', ℓ')
  omega

/-- Two non-own-color vertex jobs of the *same* vertex occupy disjoint unit intervals,
ordered by the reverse of the color order. -/
lemma vertex_sep_same {v : G.V} {ℓ ℓ' : Fin k} (h1 : ℓ ≠ G.color v) (h2 : ℓ' ≠ G.color v)
    (h : (ℓ' : ℕ) < (ℓ : ℕ)) :
    (isem G ord).d (Sum.inl (v, ℓ)) ≤ (isem G ord).start (Sum.inl (v, ℓ')) := by
  rw [start_vertex_other h2]
  change vD G ord (v, ℓ) ≤ _
  rw [vD_other G ord h1]
  omega

variable (G ord)

/-! ### 3.7 The Weight Threshold -/

/-- The threshold `W = C(k,2)·c₃ + C(k,2)·n_G·c₂ + (k-1)·n_G·c₁ + k` of Lemmas 1 and 2. -/
def targetWeight : ℕ :=
  Nat.choose k 2 * c3 G + Nat.choose k 2 * (nG G * c2 G) + (k - 1) * nG G * c1 G + k

/-! ## 4. Correctness of the reduction

The statements below are the paper's Observation 3, Lemma 1, Lemma 2 and Theorem 1,
stated over the actual construction.

Everything here is proved; the reduction's correctness is never assumed. -/

/-! ### 4.1 Lemma 1: Turning a Clique Into a Schedule -/

section Lemma1

variable {G ord}
variable {f : Fin k → G.V}

/-- The unordered color combination `{a, b}` of two distinct colors. -/
def mkPair {a b : Fin k} (h : a ≠ b) : ColorPair k :=
  if hab : a < b then ⟨(a, b), hab⟩ else ⟨(b, a), lt_of_le_of_ne (not_lt.mp hab) (Ne.symm h)⟩

lemma mkPair_spec {a b : Fin k} (h : a ≠ b) :
    ((mkPair h).lo = a ∧ (mkPair h).hi = b) ∨ ((mkPair h).lo = b ∧ (mkPair h).hi = a) := by
  unfold mkPair
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- The schedule built from a multicolored clique `f`, as in the proof of Lemma 1.

* the own-color job of a clique vertex goes on the validation machine;
* the other-color jobs of a clique vertex go on the edge selection machine of the
  corresponding color combination;
* the other-color jobs of every non-clique vertex go on the validation machine;
* the edge job of a clique edge, and the two color-combination jobs of the clique
  vertices, go on the edge selection machine of their combination;
* everything else is rejected. -/
def cliqueSchedule (f : Fin k → G.V) : (isem G ord).Schedule
  | Sum.inl (v, ℓ) =>
      if h : ℓ = G.color v then
        if v = f (G.color v) then some (validationMachine k) else none
      else
        if v = f (G.color v) then some (edgeMachine (mkPair (a := G.color v) (Ne.symm h)))
        else some (validationMachine k)
  | Sum.inr (Sum.inl e) =>
      if e.1.1 = f (G.color e.1.1) ∧ e.1.2 = f (G.color e.1.2) then
        some (edgeMachine ⟨(G.color e.1.1, G.color e.1.2), e.2.1⟩)
      else none
  | Sum.inr (Sum.inr x) =>
      if x.1.2 = f (G.color x.1.2) then some (edgeMachine x.1.1) else none

/-- Every job the clique schedule places is placed on an eligible machine. -/
theorem cliqueSchedule_elig (j : Job G) (i : Machine k)
    (h : cliqueSchedule (ord := ord) f j = some i) : i ∈ jobElig G j := by
  match j with
  | Sum.inl (v, ℓ) =>
    simp only [cliqueSchedule] at h
    split at h
    · split at h
      · cases h; exact validation_mem_vElig G _
      · exact absurd h (by simp)
    · rename_i hne
      split at h
      · cases h
        refine (mem_vElig_edge G (v, ℓ) _).mpr ?_
        rcases mkPair_spec (a := G.color v) (b := ℓ) (Ne.symm hne) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
      · cases h; exact validation_mem_vElig G _
  | Sum.inr (Sum.inl e) =>
    simp only [cliqueSchedule] at h
    split at h
    · cases h; exact Finset.mem_singleton_self _
    · exact absurd h (by simp)
  | Sum.inr (Sum.inr x) =>
    simp only [cliqueSchedule] at h
    split at h
    · cases h; exact Finset.mem_singleton_self _
    · exact absurd h (by simp)

/-- Only vertex jobs reach the validation machine, and a vertex job `j_v^{(ℓ)}` reaches
it exactly when `ℓ` is `v`'s own color iff `v` is the clique vertex of its color. -/
theorem cliqueSchedule_validation {j : Job G}
    (h : cliqueSchedule (ord := ord) f j = some (validationMachine k)) :
    ∃ v ℓ, j = Sum.inl (v, ℓ) ∧ (ℓ = G.color v ↔ v = f (G.color v)) := by
  rcases j with ⟨v, ℓ⟩ | ⟨⟨a, b⟩, hlt, he⟩ | ⟨⟨cc, z⟩, hz⟩
  · refine ⟨v, ℓ, rfl, ?_⟩
    simp only [cliqueSchedule] at h
    split at h
    · rename_i heq
      split at h
      · exact ⟨fun _ => by assumption, fun _ => heq⟩
      · simp at h
    · rename_i hne
      split at h
      · exact absurd (Option.some.inj h) (edgeMachine_ne_validation _)
      · exact ⟨fun hc => absurd hc hne, fun hc => absurd hc (by assumption)⟩
  · simp only [cliqueSchedule] at h
    split at h
    · exact absurd (Option.some.inj h) (edgeMachine_ne_validation _)
    · simp at h
  · simp only [cliqueSchedule] at h
    split at h
    · exact absurd (Option.some.inj h) (edgeMachine_ne_validation _)
    · simp at h

/-- The edge job of the clique edge realizing a color combination. -/
def cliqueEdgeJob (f : Fin k → G.V) (hf : ∀ c, G.color (f c) = c)
    (hE : ∀ a b : Fin k, a ≠ b → G.E (f a) (f b)) (c : ColorPair k) : EJob G :=
  ⟨(f c.lo, f c.hi), by rw [hf, hf]; exact c.lo_lt_hi, hE _ _ c.lo_ne_hi⟩

/-- Exactly five jobs reach the edge selection machine of a color combination `c`:
the two color-combination jobs of the clique vertices `f(ℓ)` and `f(ℓ')`, their two
cross-color vertex jobs, and the clique edge job. These are the five of Figure 1. -/
theorem cliqueSchedule_edgeMachine (hf : ∀ c, G.color (f c) = c)
    (hE : ∀ a b : Fin k, a ≠ b → G.E (f a) (f b)) {c : ColorPair k} {j : Job G}
    (h : cliqueSchedule (ord := ord) f j = some (edgeMachine c)) :
    j = Sum.inr (Sum.inr ⟨(c, f c.lo), Or.inl (hf c.lo)⟩)
      ∨ j = Sum.inl (f c.lo, c.hi)
      ∨ j = Sum.inr (Sum.inl (cliqueEdgeJob f hf hE c))
      ∨ j = Sum.inl (f c.hi, c.lo)
      ∨ j = Sum.inr (Sum.inr ⟨(c, f c.hi), Or.inr (hf c.hi)⟩) := by
  rcases j with ⟨v, ℓ⟩ | ⟨⟨a, b⟩, hlt, he⟩ | ⟨⟨cc, z⟩, hz⟩
  · simp only [cliqueSchedule] at h
    split at h
    · split at h
      · exact absurd (Option.some.inj h) (Ne.symm (edgeMachine_ne_validation _))
      · simp at h
    · rename_i hne
      split at h
      · rename_i hv
        have hpair : mkPair (a := G.color v) (b := ℓ) (Ne.symm hne) = c :=
          Option.some.inj (Option.some.inj h)
        rcases mkPair_spec (a := G.color v) (b := ℓ) (Ne.symm hne) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hpair] at h1 h2
          refine Or.inr (Or.inl ?_)
          have hvv : v = f c.lo := by rw [h1]; exact hv
          rw [hvv, ← h2]
        · rw [hpair] at h1 h2
          refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          have hvv : v = f c.hi := by rw [h2]; exact hv
          rw [hvv, ← h1]
      · exact absurd (Option.some.inj h) (Ne.symm (edgeMachine_ne_validation _))
  · simp only [cliqueSchedule] at h
    split at h
    · rename_i hcond
      obtain ⟨hca, hcb⟩ := hcond
      have hc : (⟨(G.color a, G.color b), hlt⟩ : ColorPair k) = c :=
        Option.some.inj (Option.some.inj h)
      have hlo : G.color a = c.lo := congrArg ColorPair.lo hc
      have hhi : G.color b = c.hi := congrArg ColorPair.hi hc
      refine Or.inr (Or.inr (Or.inl ?_))
      have h1 : a = f c.lo := by rw [hca, hlo]
      have h2 : b = f c.hi := by rw [hcb, hhi]
      subst h1; subst h2
      rfl
    · simp at h
  · simp only [cliqueSchedule] at h
    split at h
    · rename_i hzz
      have hc : cc = c := Option.some.inj (Option.some.inj h)
      subst hc
      rcases hz with hlo | hhi
      · refine Or.inl ?_
        have h1 : z = f cc.lo := by rw [hzz, hlo]
        subst h1
        rfl
      · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        have h1 : z = f cc.hi := by rw [hzz, hhi]
        subst h1
        rfl
    · simp at h

/-- **The clique schedule is feasible.** On each edge selection machine the five
scheduled jobs tile consecutively (`edgeMachine_layout`); on the validation machine the
scheduled jobs are vertex jobs of `π`-distinct vertices, or distinct non-own colors of
one vertex, and are separated either way. -/
theorem cliqueSchedule_feasible (hf : ∀ c, G.color (f c) = c)
    (hE : ∀ a b : Fin k, a ≠ b → G.E (f a) (f b)) :
    (isem G ord).Feasible (cliqueSchedule (ord := ord) f) := by
  refine ⟨cliqueSchedule_elig, ?_⟩
  intro j j' i hne hconf hj hj'
  refine absurd hconf ?_
  cases i with
  | none =>
    obtain ⟨v, ℓ, rfl, hiff⟩ := cliqueSchedule_validation hj
    obtain ⟨v', ℓ', rfl, hiff'⟩ := cliqueSchedule_validation hj'
    rcases lt_trichotomy (ord.π v) (ord.π v') with hlt | heq | hgt
    · exact (isem G ord).not_conflict_of_le (vertex_sep_of_π_lt ℓ ℓ' hlt)
    · have hvv : v = v' := ord.π_inj heq
      subst hvv
      have hll : ℓ ≠ ℓ' := by rintro rfl; exact hne rfl
      have h1 : ℓ ≠ G.color v := fun hc => hll (hc.trans (hiff'.mpr (hiff.mp hc)).symm)
      have h2 : ℓ' ≠ G.color v := fun hc => hll ((hiff.mpr (hiff'.mp hc)).trans hc.symm)
      rcases lt_or_gt_of_ne (show (ℓ : ℕ) ≠ (ℓ' : ℕ) from fun hc => hll (Fin.ext hc)) with hc | hc
      · exact fun hcf => (isem G ord).not_conflict_of_le (vertex_sep_same h2 h1 hc)
          ((isem G ord).conflict_symm hcf)
      · exact (isem G ord).not_conflict_of_le (vertex_sep_same h1 h2 hc)
    · exact fun hcf => (isem G ord).not_conflict_of_le (vertex_sep_of_π_lt ℓ' ℓ hgt)
        ((isem G ord).conflict_symm hcf)
  | some c =>
    have hlt : G.color (f c.lo) < G.color (f c.hi) := by rw [hf, hf]; exact c.lo_lt_hi
    have hlay := edgeMachine_layout (ord := ord) (hu := hf c.lo) (hv := hf c.hi) hlt
      (hE _ _ c.lo_ne_hi)
    exact (isem G ord).not_conflict_of_chain5 hlay.1 hlay.2.1 hlay.2.2.1 hlay.2.2.2
      (cliqueSchedule_edgeMachine hf hE hj) (cliqueSchedule_edgeMachine hf hE hj') hne

/-! #### The weight of the clique schedule -/

section Weight

variable (hf : ∀ c, G.color (f c) = c)

include hf in
lemma f_inj : Function.Injective f := fun a b hab => by rw [← hf a, ← hf b, hab]

include hf in
/-- There are exactly `k` clique vertices, one per color. -/
lemma cliqueVertices_card :
    (Finset.univ.filter (fun v : G.V => v = f (G.color v))).card = k := by
  have himg : (Finset.univ.filter (fun v : G.V => v = f (G.color v)))
      = Finset.image f Finset.univ := by
    ext v
    constructor
    · intro hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact Finset.mem_image.mpr ⟨G.color v, Finset.mem_univ _, hv.symm⟩
    · intro hv
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hf]
  rw [himg, Finset.card_image_of_injective _ (f_inj hf), Finset.card_univ, Fintype.card_fin]

set_option linter.unusedSimpArgs false in
/-- The contribution of a single vertex job to the weight of the clique schedule. -/
lemma cliqueSchedule_w_vertex (v : G.V) (ℓ : Fin k) :
    (cliqueSchedule (ord := ord) f (Sum.inl (v, ℓ))).elim 0
        (fun _ => (isem G ord).w (Sum.inl (v, ℓ)))
      = if ℓ = G.color v then (if v = f (G.color v) then 1 else 0) else c1 G := by
  by_cases h : ℓ = G.color v
  · subst h
    simp only [cliqueSchedule, dif_pos rfl, if_pos rfl]
    by_cases h2 : v = f (G.color v)
    · rw [if_pos h2, if_pos h2]
      change vW G (v, G.color v) = 1
      exact vW_own G v
    · rw [if_neg h2, if_neg h2]
      rfl
  · simp only [cliqueSchedule, dif_neg h, if_neg h]
    by_cases h2 : v = f (G.color v)
    · rw [if_pos h2]
      change vW G (v, ℓ) = c1 G
      exact vW_other G h
    · rw [if_neg h2]
      change vW G (v, ℓ) = c1 G
      exact vW_other G h

/-- Summing an expression that takes one value at a single color and a constant
elsewhere. -/
private lemma sum_single_const (A B : ℕ) (b : Fin k) :
    (∑ ℓ : Fin k, if ℓ = b then A else B) = A + (k - 1) * B := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), if_pos rfl]
  congr 1
  rw [Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

include hf in
/-- Every vertex job of a non-clique vertex, and every cross-color job of a clique
vertex, is scheduled; the own-color job is scheduled exactly for the `k` clique
vertices. Total: `k + n_G(k-1)c₁`. -/
theorem cliqueSchedule_weight_vertices :
    (∑ x : VJob G, (cliqueSchedule (ord := ord) f (Sum.inl x)).elim 0
        (fun _ => (isem G ord).w (Sum.inl x)))
      = k + nG G * ((k - 1) * c1 G) := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ v : G.V,
      (∑ ℓ : Fin k, (cliqueSchedule (ord := ord) f (Sum.inl (v, ℓ))).elim 0
          (fun _ => (isem G ord).w (Sum.inl (v, ℓ))))
        = (if v = f (G.color v) then 1 else 0) + (k - 1) * c1 G := by
    intro v
    rw [Finset.sum_congr rfl (fun ℓ _ => cliqueSchedule_w_vertex (ord := ord) v ℓ)]
    exact sum_single_const (if v = f (G.color v) then 1 else 0) (c1 G) (G.color v)
  rw [Finset.sum_congr rfl (fun v _ => hinner v), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_boole,
    cliqueVertices_card hf, Nat.cast_id]
  simp only [nG]

/-- The contribution of a single edge job to the weight of the clique schedule. -/
lemma cliqueSchedule_w_edge (e : EJob G) :
    (cliqueSchedule (ord := ord) f (Sum.inr (Sum.inl e))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inl e)))
      = if e.1.1 = f (G.color e.1.1) ∧ e.1.2 = f (G.color e.1.2) then eW G ord e else 0 := by
  by_cases hc : e.1.1 = f (G.color e.1.1) ∧ e.1.2 = f (G.color e.1.2)
  · simp only [cliqueSchedule, if_pos hc]; rfl
  · simp only [cliqueSchedule, if_neg hc]; rfl

include hf in
lemma cliqueEdgeJob_inj (hE : ∀ a b : Fin k, a ≠ b → G.E (f a) (f b)) :
    Function.Injective (cliqueEdgeJob f hf hE) := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
  have hv : ((f a, f b) : G.V × G.V) = (f a', f b') := congrArg Subtype.val h
  have h1 : a = a' := f_inj hf (congrArg Prod.fst hv)
  have h2 : b = b' := f_inj hf (congrArg Prod.snd hv)
  subst h1; subst h2; rfl

include hf in
lemma filter_edge_eq_image (hE : ∀ a b : Fin k, a ≠ b → G.E (f a) (f b)) :
    (Finset.univ.filter (fun e : EJob G =>
        e.1.1 = f (G.color e.1.1) ∧ e.1.2 = f (G.color e.1.2)))
      = Finset.image (cliqueEdgeJob f hf hE) Finset.univ := by
  ext e
  constructor
  · intro he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    refine Finset.mem_image.mpr
      ⟨⟨(G.color e.1.1, G.color e.1.2), e.2.1⟩, Finset.mem_univ _, ?_⟩
    obtain ⟨⟨a, b⟩, hlt, he'⟩ := e
    obtain ⟨h1, h2⟩ := he
    apply Subtype.ext
    dsimp only [cliqueEdgeJob, ColorPair.lo, ColorPair.hi] at *
    rw [← h1, ← h2]
  · intro he
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by change f c.lo = f (G.color (f c.lo)); rw [hf],
           by change f c.hi = f (G.color (f c.hi)); rw [hf]⟩

include hf in
/-- Exactly one edge job is scheduled per color combination: the clique edge. -/
theorem cliqueSchedule_weight_edges (hE : ∀ a b : Fin k, a ≠ b → G.E (f a) (f b)) :
    (∑ e : EJob G, (cliqueSchedule (ord := ord) f (Sum.inr (Sum.inl e))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inl e))))
      = ∑ c : ColorPair k, (c2 G * (ord.π (f c.hi) - ord.π (f c.lo)) + c3 G) := by
  rw [Finset.sum_congr rfl (fun e _ => cliqueSchedule_w_edge (ord := ord) e),
    ← Finset.sum_filter, filter_edge_eq_image hf hE,
    Finset.sum_image (fun x _ y _ h => cliqueEdgeJob_inj hf hE h)]
  rfl

/-- The two color-combination jobs of a combination that the clique schedule keeps. -/
def combIdx (f : Fin k → G.V) (hf : ∀ c, G.color (f c) = c) :
    ColorPair k ⊕ ColorPair k → CJob G
  | Sum.inl c => ⟨(c, f c.lo), Or.inl (hf c.lo)⟩
  | Sum.inr c => ⟨(c, f c.hi), Or.inr (hf c.hi)⟩

include hf in
lemma combIdx_inj : Function.Injective (combIdx f hf) := by
  have key : ∀ c c' : ColorPair k, c = c' → f c.lo = f c'.hi → False := by
    rintro c c' rfl h1
    exact c.lo_ne_hi (f_inj hf h1)
  rintro (c | c) (c' | c') h <;>
    (have hv := congrArg Subtype.val h
     simp only [combIdx, Prod.mk.injEq] at hv)
  · rw [hv.1]
  · exact absurd hv.2 (fun hh => key c c' hv.1 hh)
  · exact absurd hv.2.symm (fun hh => key c' c hv.1.symm hh)
  · rw [hv.1]

include hf in
lemma filter_comb_eq_image :
    (Finset.univ.filter (fun x : CJob G => x.1.2 = f (G.color x.1.2)))
      = Finset.image (combIdx f hf) Finset.univ := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨cc, z⟩, hz⟩ := x
    dsimp only at hx
    rcases hz with hlo | hhi
    · dsimp only at hlo
      refine Finset.mem_image.mpr ⟨Sum.inl cc, Finset.mem_univ _, ?_⟩
      have hzz : z = f cc.lo := by rw [← hlo]; exact hx
      subst hzz
      rfl
    · dsimp only at hhi
      refine Finset.mem_image.mpr ⟨Sum.inr cc, Finset.mem_univ _, ?_⟩
      have hzz : z = f cc.hi := by rw [← hhi]; exact hx
      subst hzz
      rfl
  · intro hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases c with
    | inl c => change f c.lo = f (G.color (f c.lo)); rw [hf]
    | inr c => change f c.hi = f (G.color (f c.hi)); rw [hf]

/-- The contribution of a single color-combination job to the weight. -/
lemma cliqueSchedule_w_comb (x : CJob G) :
    (cliqueSchedule (ord := ord) f (Sum.inr (Sum.inr x))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inr x)))
      = if x.1.2 = f (G.color x.1.2) then cW G ord x else 0 := by
  by_cases hc : x.1.2 = f (G.color x.1.2)
  · simp only [cliqueSchedule, if_pos hc]; rfl
  · simp only [cliqueSchedule, if_neg hc]; rfl

include hf in
/-- Both color-combination jobs of each combination's two clique vertices are
scheduled, contributing `c₂·π(f ℓ) + c₂·(n_G - π(f ℓ'))`. -/
theorem cliqueSchedule_weight_combs :
    (∑ x : CJob G, (cliqueSchedule (ord := ord) f (Sum.inr (Sum.inr x))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inr x))))
      = (∑ c : ColorPair k, c2 G * ord.π (f c.lo))
        + ∑ c : ColorPair k, c2 G * (nG G - ord.π (f c.hi)) := by
  rw [Finset.sum_congr rfl (fun x _ => cliqueSchedule_w_comb (ord := ord) x),
    ← Finset.sum_filter, filter_comb_eq_image hf,
    Finset.sum_image (fun x _ y _ h => combIdx_inj hf h), Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    exact cW_lo G ord (combIdx f hf (Sum.inl c)) (hf c.lo)
  · refine Finset.sum_congr rfl fun c _ => ?_
    refine cW_hi G ord (combIdx f hf (Sum.inr c)) ?_
    change ¬ G.color (f c.hi) = c.lo
    rw [hf]
    exact fun hc => c.lo_ne_hi hc.symm

include hf in
/-- **The clique schedule attains exactly the threshold weight `W`.** -/
theorem cliqueSchedule_weight (hE : ∀ a b : Fin k, a ≠ b → G.E (f a) (f b)) :
    (isem G ord).weight (cliqueSchedule (ord := ord) f) = targetWeight G := by
  have hterm : ∀ c : ColorPair k,
      (c2 G * (ord.π (f c.hi) - ord.π (f c.lo)) + c3 G)
          + (c2 G * ord.π (f c.lo) + c2 G * (nG G - ord.π (f c.hi)))
        = c3 G + nG G * c2 G := by
    intro c
    have hlt : G.color (f c.lo) < G.color (f c.hi) := by rw [hf, hf]; exact c.lo_lt_hi
    have ha : ord.π (f c.lo) ≤ ord.π (f c.hi) := le_of_lt (ord.π_mono _ _ hlt)
    have hb : ord.π (f c.hi) ≤ nG G := ord.π_le _
    have e1 : c2 G * (ord.π (f c.hi) - ord.π (f c.lo)) + c2 G * ord.π (f c.lo)
        = c2 G * ord.π (f c.hi) := by
      rw [← Nat.mul_add]; congr 1; omega
    have e2 : c2 G * ord.π (f c.hi) + c2 G * (nG G - ord.π (f c.hi)) = c2 G * nG G := by
      rw [← Nat.mul_add]; congr 1; omega
    have e3 : c2 G * nG G = nG G * c2 G := Nat.mul_comm _ _
    omega
  have hcombined : (∑ c : ColorPair k, (c2 G * (ord.π (f c.hi) - ord.π (f c.lo)) + c3 G))
      + ((∑ c : ColorPair k, c2 G * ord.π (f c.lo))
        + ∑ c : ColorPair k, c2 G * (nG G - ord.π (f c.hi)))
      = Nat.choose k 2 * (c3 G + nG G * c2 G) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ,
      card_colorPair, smul_eq_mul]
  change (∑ j : Job G, (cliqueSchedule (ord := ord) f j).elim 0
      (fun _ => (isem G ord).w j)) = targetWeight G
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, cliqueSchedule_weight_vertices hf,
    cliqueSchedule_weight_edges hf hE, cliqueSchedule_weight_combs hf, hcombined]
  simp only [targetWeight]
  ring

end Weight

end Lemma1

/-! ### 4.2 Observation 3 -/

section Observation3

variable {G ord}

/-- The color combination of an edge job: the only machine it is eligible on. -/
def epair (e : EJob G) : ColorPair k := ⟨(G.color e.1.1, G.color e.1.2), e.2.1⟩

lemma edgeJob_machine {σ : (isem G ord).Schedule} (hfeas : (isem G ord).Feasible σ)
    {e : EJob G} {i : Machine k} (h : σ (Sum.inr (Sum.inl e)) = some i) :
    i = edgeMachine (epair e) :=
  Finset.mem_singleton.mp (hfeas.1 _ _ h)

/-- All edge jobs of one color combination pairwise conflict, so at most one of them
can be scheduled on the corresponding edge selection machine. -/
lemma edge_conflict {e e' : EJob G} (h : epair e = epair e') :
    (isem G ord).Conflict (Sum.inr (Sum.inl e)) (Sum.inr (Sum.inl e')) := by
  have key : ∀ a b : EJob G, G.color a.1.1 = G.color b.1.1 →
      (isem G ord).start (Sum.inr (Sum.inl a)) < (isem G ord).d (Sum.inr (Sum.inl b)) := by
    intro a b h1
    have hcolor : G.color a.1.1 < G.color b.1.2 := by rw [h1]; exact b.2.1
    have hπ : ord.π a.1.1 < ord.π b.1.2 := ord.π_mono _ _ hcolor
    have hstep : (k + 2) * ord.π a.1.1 + (k + 2) ≤ (k + 2) * ord.π b.1.2 := by
      have h2 : ord.π a.1.1 + 1 ≤ ord.π b.1.2 := hπ
      calc (k + 2) * ord.π a.1.1 + (k + 2) = (k + 2) * (ord.π a.1.1 + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
        _ ≤ (k + 2) * ord.π b.1.2 := Nat.mul_le_mul le_rfl h2
    have hcb : (G.color b.1.1 : ℕ) < k := (G.color b.1.1).isLt
    rw [start_edge]
    change _ < eD G ord b
    simp only [eD]
    omega
  exact ⟨key e e' (congrArg ColorPair.lo h), key e' e (congrArg ColorPair.lo h).symm⟩

lemma edge_unique {σ : (isem G ord).Schedule} (hfeas : (isem G ord).Feasible σ)
    {e e' : EJob G} {i : Machine k}
    (h : σ (Sum.inr (Sum.inl e)) = some i) (h' : σ (Sum.inr (Sum.inl e')) = some i) :
    e = e' := by
  by_contra hne
  have hp : epair e = epair e' :=
    edgeMachine_inj ((edgeJob_machine hfeas h).symm.trans (edgeJob_machine hfeas h'))
  exact hfeas.2 _ _ i (fun hh => hne (Sum.inl.inj (Sum.inr.inj hh))) (edge_conflict hp) h h'

/-! #### Weight bounds on the individual job families -/

lemma totalVertexWeight : (∑ x : VJob G, vW G x) = nG G * (1 + (k - 1) * c1 G) := by
  rw [Fintype.sum_prod_type]
  have hv : ∀ v : G.V, (∑ ℓ : Fin k, vW G (v, ℓ)) = 1 + (k - 1) * c1 G := by
    intro v
    simp only [vW]
    exact sum_single_const 1 (c1 G) (G.color v)
  rw [Finset.sum_congr rfl (fun v _ => hv v), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rfl

lemma cW_le (x : CJob G) : cW G ord x ≤ nG G * c2 G := by
  simp only [cW]
  have h1 := ord.π_le x.1.2
  split
  · rw [Nat.mul_comm (c2 G)]; exact Nat.mul_le_mul h1 le_rfl
  · rw [Nat.mul_comm (c2 G)]; exact Nat.mul_le_mul (by omega) le_rfl

lemma eW_le (e : EJob G) : eW G ord e ≤ nG G * c2 G + c3 G := by
  simp only [eW]
  have h1 : ord.π e.1.2 - ord.π e.1.1 ≤ nG G := le_trans (Nat.sub_le _ _) (ord.π_le _)
  have : c2 G * (ord.π e.1.2 - ord.π e.1.1) ≤ nG G * c2 G := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul h1 le_rfl
  omega

lemma totalCombWeight_le :
    (∑ x : CJob G, cW G ord x) ≤ Nat.choose k 2 * nG G * (nG G * c2 G) := by
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ (fun x _ => cW_le x)) ?_
  rw [smul_eq_mul, Finset.card_univ]
  refine Nat.mul_le_mul_right _ ?_
  have h1 : Fintype.card (CJob G) ≤ Fintype.card (ColorPair k × G.V) :=
    Fintype.card_subtype_le _
  rw [Fintype.card_prod, card_colorPair] at h1
  exact h1

private lemma two_choose_two (m : ℕ) : 2 * Nat.choose m 2 = m * (m - 1) := by
  have h := Finset.sum_range_id_mul_two m
  rw [Nat.choose_two_right]
  omega

/-- The arithmetic core of Observation 3: everything except `C(k,2)` copies of `c₃`
fits strictly below one `c₃`. -/
private lemma obs3_arith (hN : 1 ≤ nG G) (hC : 1 ≤ Nat.choose k 2) :
    nG G * (1 + (k - 1) * c1 G)
      + ((Nat.choose k 2 - 1) * (nG G * c2 G) + Nat.choose k 2 * nG G * (nG G * c2 G))
      < c3 G := by
  obtain ⟨D, hD⟩ : ∃ D, Nat.choose k 2 = D + 1 := ⟨Nat.choose k 2 - 1, by omega⟩
  have hB1 : 1 + (k - 1) * c1 G ≤ c2 G := by
    have h1 : (k - 1) * 1 ≤ (k - 1) * nG G := Nat.mul_le_mul le_rfl hN
    rw [Nat.mul_one] at h1
    have h2 : (k - 1) * c1 G ≤ (k - 1) * nG G * c1 G := Nat.mul_le_mul h1 le_rfl
    simp only [c2]
    omega
  have hNB : c2 G ≤ nG G * c2 G := by
    calc c2 G = 1 * c2 G := (Nat.one_mul _).symm
      _ ≤ nG G * c2 G := Nat.mul_le_mul hN le_rfl
  have h1 : nG G * (1 + (k - 1) * c1 G) ≤ nG G * (nG G * c2 G) :=
    Nat.mul_le_mul le_rfl (le_trans hB1 hNB)
  have h2 : D * (nG G * c2 G) ≤ D * (nG G * (nG G * c2 G)) :=
    Nat.mul_le_mul le_rfl (by
      calc nG G * c2 G = 1 * (nG G * c2 G) := (Nat.one_mul _).symm
        _ ≤ nG G * (nG G * c2 G) := Nat.mul_le_mul hN le_rfl)
  have h3 : (D + 1) * nG G * (nG G * c2 G) = (D + 1) * (nG G * (nG G * c2 G)) := by ring
  have hc3 : c3 G = (k + k ^ 2) * (nG G * (nG G * c2 G)) + 1 := by simp only [c3]; ring
  have h2C : 2 * (D + 1) ≤ k + k ^ 2 := by
    have ht := two_choose_two k
    have hkk : k * (k - 1) ≤ k ^ 2 :=
      le_trans (Nat.mul_le_mul le_rfl (by omega : k - 1 ≤ k)) (le_of_eq (Nat.pow_two k).symm)
    omega
  have hfinal : 2 * (D + 1) * (nG G * (nG G * c2 G))
      ≤ (k + k ^ 2) * (nG G * (nG G * c2 G)) := Nat.mul_le_mul h2C le_rfl
  have hsum : nG G * (nG G * c2 G) + D * (nG G * (nG G * c2 G))
      + (D + 1) * (nG G * (nG G * c2 G)) = 2 * (D + 1) * (nG G * (nG G * c2 G)) := by ring
  rw [hD]
  simp only [Nat.add_sub_cancel]
  omega

end Observation3

/-- **Observation 3.** Any feasible schedule reaching the threshold schedules exactly
`C(k,2)` edge jobs, one on each edge selection machine. -/
theorem observation3 (σ : (isem G ord).Schedule)
    (hfeas : (isem G ord).Feasible σ)
    (hW : targetWeight G ≤ (isem G ord).weight σ) :
    ∀ c : ColorPair k, ∃! e : EJob G,
      σ (Sum.inr (Sum.inl e) : Job G) = some (edgeMachine c) := by
  intro c₀
  -- The existence of a color combination forces `k ≥ 2`, hence `C(k,2) ≥ 1`.
  have hk2 : 2 ≤ k := by
    have h1 : (c₀.lo : ℕ) < (c₀.hi : ℕ) := c₀.lo_lt_hi
    have h2 := c₀.hi.isLt
    omega
  have hCpos : 1 ≤ Nat.choose k 2 := Nat.choose_pos hk2
  -- `G` has at least one vertex, else nothing can be scheduled at all.
  have hN : 1 ≤ nG G := by
    by_contra hn
    have hemp : IsEmpty G.V := Fintype.card_eq_zero_iff.mp (by simpa [nG] using hn)
    have hw0 : (isem G ord).weight σ = 0 := by
      change (∑ j : Job G, _) = 0
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases j with ⟨v, _⟩ | ⟨⟨u, _⟩, _⟩ | ⟨⟨_, z⟩, _⟩
      · exact (hemp.false v).elim
      · exact (hemp.false u).elim
      · exact (hemp.false z).elim
    rw [hw0] at hW
    simp only [targetWeight] at hW
    omega
  -- The set of scheduled edge jobs.
  classical
  set S : Finset (EJob G) :=
    Finset.univ.filter (fun e => (σ (Sum.inr (Sum.inl e))).isSome = true) with hSdef
  have hmemS : ∀ e : EJob G, e ∈ S ↔ (σ (Sum.inr (Sum.inl e))).isSome = true := by
    intro e; rw [hSdef]; simp
  -- Splitting the objective over the three job families.
  have hsplit : (isem G ord).weight σ
      = (∑ x : VJob G, (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x)))
        + ((∑ e : EJob G, (σ (Sum.inr (Sum.inl e))).elim 0
              (fun _ => (isem G ord).w (Sum.inr (Sum.inl e))))
          + ∑ x : CJob G, (σ (Sum.inr (Sum.inr x))).elim 0
              (fun _ => (isem G ord).w (Sum.inr (Sum.inr x)))) := by
    change (∑ j : Job G, (σ j).elim 0 (fun _ => (isem G ord).w j)) = _
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hV : (∑ x : VJob G, (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x)))
      ≤ nG G * (1 + (k - 1) * c1 G) := by
    rw [← totalVertexWeight (G := G)]
    exact Finset.sum_le_sum fun x _ => by cases σ (Sum.inl x) <;> simp
  have hCsum : (∑ x : CJob G, (σ (Sum.inr (Sum.inr x))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inr x))))
      ≤ Nat.choose k 2 * nG G * (nG G * c2 G) :=
    le_trans (Finset.sum_le_sum fun x _ => by
      cases σ (Sum.inr (Sum.inr x)) <;> simp) (totalCombWeight_le (ord := ord))
  have hEsum : (∑ e : EJob G, (σ (Sum.inr (Sum.inl e))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inl e))))
      ≤ S.card * (nG G * c2 G + c3 G) := by
    have hz : ∀ e ∈ (Finset.univ : Finset (EJob G)), e ∉ S →
        (σ (Sum.inr (Sum.inl e))).elim 0 (fun _ => (isem G ord).w (Sum.inr (Sum.inl e))) = 0 := by
      intro e _ he
      rw [hmemS] at he
      cases h : σ (Sum.inr (Sum.inl e))
      · rfl
      · rw [h] at he; simp at he
    rw [← Finset.sum_subset (Finset.subset_univ S) hz, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun e _ => ?_
    cases σ (Sum.inr (Sum.inl e))
    · simp
    · simpa using eW_le (ord := ord) e
  -- `epair` is injective on the scheduled edge jobs.
  have hinj : ∀ e ∈ S, ∀ e' ∈ S, epair e = epair e' → e = e' := by
    intro e he e' he' hp
    rw [hmemS] at he he'
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp he
    obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp he'
    rw [edgeJob_machine hfeas hi] at hi
    rw [edgeJob_machine hfeas hi', ← hp] at hi'
    exact edge_unique hfeas hi hi'
  have hcard_le : S.card ≤ Fintype.card (ColorPair k) := by
    have h1 : (S.image epair).card = S.card :=
      Finset.card_image_of_injOn (fun a ha b hb => hinj a ha b hb)
    rw [← h1, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  -- Fewer than `C(k,2)` scheduled edge jobs cannot reach the threshold.
  have hcard_ge : Fintype.card (ColorPair k) ≤ S.card := by
    by_contra hlt
    rw [Nat.not_le, card_colorPair] at hlt
    have hSle : S.card ≤ Nat.choose k 2 - 1 := by omega
    have hbound : (isem G ord).weight σ
        ≤ nG G * (1 + (k - 1) * c1 G)
          + ((Nat.choose k 2 - 1) * (nG G * c2 G + c3 G)
             + Nat.choose k 2 * nG G * (nG G * c2 G)) := by
      rw [hsplit]
      exact Nat.add_le_add hV
        (Nat.add_le_add (le_trans hEsum (Nat.mul_le_mul hSle le_rfl)) hCsum)
    have hexp : (Nat.choose k 2 - 1) * (nG G * c2 G + c3 G)
        = (Nat.choose k 2 - 1) * (nG G * c2 G) + (Nat.choose k 2 - 1) * c3 G := Nat.mul_add _ _ _
    have harith := obs3_arith (G := G) hN hCpos
    have htarget : Nat.choose k 2 * c3 G ≤ targetWeight G := by
      simp only [targetWeight]; omega
    have hCsplit : Nat.choose k 2 * c3 G = (Nat.choose k 2 - 1) * c3 G + c3 G := by
      have h1 : Nat.choose k 2 - 1 + 1 = Nat.choose k 2 := by omega
      calc Nat.choose k 2 * c3 G = (Nat.choose k 2 - 1 + 1) * c3 G := by rw [h1]
        _ = (Nat.choose k 2 - 1) * c3 G + c3 G := by ring
    omega
  -- Hence exactly one scheduled edge job per machine.
  have hcard : S.card = Fintype.card (ColorPair k) := le_antisymm hcard_le hcard_ge
  have himg : S.image epair = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_image_of_injOn (fun a ha b hb => hinj a ha b hb), hcard]
  obtain ⟨e, heS, hep⟩ :=
    Finset.mem_image.mp (show c₀ ∈ S.image epair by rw [himg]; exact Finset.mem_univ c₀)
  have heS' := (hmemS e).mp heS
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp heS'
  rw [edgeJob_machine hfeas hi, hep] at hi
  exact ⟨e, hi, fun e' he' => edge_unique hfeas he' hi⟩

/-- **Lemma 1.** A multicolored clique of size `k` yields a feasible schedule of total
weight at least `W`. -/
theorem lemma1 (hclique : G.HasClique) : (isem G ord).HasWeight (targetWeight G) := by
  obtain ⟨f, hf, hE⟩ := hclique
  exact ⟨cliqueSchedule (ord := ord) f, cliqueSchedule_feasible hf hE,
    le_of_eq (cliqueSchedule_weight hf hE).symm⟩

/-! ### 4.3 Lemma 2 — interval geometry on an edge selection machine

Six facts of the form "these two jobs sit on the same machine, so their intervals are
separated, so their vertices are `π`-ordered this way". Together with the weight
accounting below they pin down exactly which jobs an optimal schedule uses. -/

section Lemma2

variable {G ord}

lemma not_conflict_iff {I : ISEM} {j j' : I.Job} :
    ¬ I.Conflict j j' ↔ I.d j' ≤ I.start j ∨ I.d j ≤ I.start j' := by
  unfold ISEM.Conflict
  omega

lemma sep_of_same_machine {σ : (isem G ord).Schedule} (hfeas : (isem G ord).Feasible σ)
    {j j' : Job G} {i : Machine k} (hne : j ≠ j')
    (h : σ j = some i) (h' : σ j' = some i) :
    (isem G ord).d j' ≤ (isem G ord).start j ∨ (isem G ord).d j ≤ (isem G ord).start j' :=
  not_conflict_iff.mp (fun hc => hfeas.2 j j' i hne hc h h')

/-- Cancelling the common factor `K ≥ 2` from `K·a ≤ K·b + 1`. -/
private lemma pi_le_of_le_succ {K a b : ℕ} (hK : 2 ≤ K) (h : K * a ≤ K * b + 1) : a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  have h2 : K * (b + 1) ≤ K * a := Nat.mul_le_mul le_rfl hba
  rw [Nat.mul_add, Nat.mul_one] at h2
  omega

variable {σ : (isem G ord).Schedule} (hfeas : (isem G ord).Feasible σ)

include hfeas in
/-- The `V_l`-side combination job scheduled with an edge job belongs to a vertex at or
before the edge job's low endpoint. -/
lemma comb_lo_le {c : ColorPair k} {z : G.V} {hz : G.color z = c.lo} {e : EJob G}
    (hep : epair e = c)
    (h1 : σ (Sum.inr (Sum.inr ⟨(c, z), Or.inl hz⟩)) = some (edgeMachine c))
    (h2 : σ (Sum.inr (Sum.inl e)) = some (edgeMachine c)) :
    ord.π z ≤ ord.π e.1.1 := by
  have hne : (Sum.inr (Sum.inr ⟨(c, z), Or.inl hz⟩) : Job G) ≠ Sum.inr (Sum.inl e) := by simp
  have hsep := sep_of_same_machine hfeas hne h1 h2
  have hsA : (isem G ord).start (Sum.inr (Sum.inr ⟨(c, z), Or.inl hz⟩)) = 1 :=
    start_comb_lo _ hz
  have hdA : (isem G ord).d (Sum.inr (Sum.inr ⟨(c, z), Or.inl hz⟩))
      = (k + 2) * ord.π z - (c.hi : ℕ) - 1 := cD_lo G ord _ hz
  have hsB : (isem G ord).start (Sum.inr (Sum.inl e))
      = (k + 2) * ord.π e.1.1 - (G.color e.1.2 : ℕ) := start_edge e
  have hdB : (isem G ord).d (Sum.inr (Sum.inl e))
      = (k + 2) * ord.π e.1.2 - (G.color e.1.1 : ℕ) - 1 := rfl
  have hcolo : G.color e.1.1 = c.lo := congrArg ColorPair.lo hep
  have hcohi : G.color e.1.2 = c.hi := congrArg ColorPair.hi hep
  have hKz := K_le_Kpi (ord := ord) z
  have hKu := K_le_Kpi (ord := ord) e.1.1
  have hKv := K_le_Kpi (ord := ord) e.1.2
  have hlo : (c.lo : ℕ) < k := c.lo.isLt
  have hhi : (c.hi : ℕ) < k := c.hi.isLt
  rw [hsA, hdA, hsB, hdB, hcolo, hcohi] at hsep
  exact pi_le_of_le_succ (K := k + 2) (by omega) (by omega)

include hfeas in
/-- The `V_l'`-side combination job scheduled with an edge job belongs to a vertex at
or after the edge job's high endpoint. -/
lemma comb_hi_ge {c : ColorPair k} {z : G.V} {hz : G.color z = c.hi} {e : EJob G}
    (hep : epair e = c)
    (h1 : σ (Sum.inr (Sum.inr ⟨(c, z), Or.inr hz⟩)) = some (edgeMachine c))
    (h2 : σ (Sum.inr (Sum.inl e)) = some (edgeMachine c)) :
    ord.π e.1.2 ≤ ord.π z := by
  have hnelohi : ¬ G.color z = c.lo := by rw [hz]; exact fun hc => c.lo_ne_hi hc.symm
  have hne : (Sum.inr (Sum.inr ⟨(c, z), Or.inr hz⟩) : Job G) ≠ Sum.inr (Sum.inl e) := by simp
  have hsep := sep_of_same_machine hfeas hne h1 h2
  have hsA : (isem G ord).start (Sum.inr (Sum.inr ⟨(c, z), Or.inr hz⟩))
      = (k + 2) * ord.π z - (c.lo : ℕ) := start_comb_hi _ hnelohi
  have hdA : (isem G ord).d (Sum.inr (Sum.inr ⟨(c, z), Or.inr hz⟩))
      = (k + 2) * nG G + 2 := cD_hi G ord _ hnelohi
  have hsB : (isem G ord).start (Sum.inr (Sum.inl e))
      = (k + 2) * ord.π e.1.1 - (G.color e.1.2 : ℕ) := start_edge e
  have hdB : (isem G ord).d (Sum.inr (Sum.inl e))
      = (k + 2) * ord.π e.1.2 - (G.color e.1.1 : ℕ) - 1 := rfl
  have hcolo : G.color e.1.1 = c.lo := congrArg ColorPair.lo hep
  have hcohi : G.color e.1.2 = c.hi := congrArg ColorPair.hi hep
  have hKz := K_le_Kpi (ord := ord) z
  have hKu := K_le_Kpi (ord := ord) e.1.1
  have hKv := K_le_Kpi (ord := ord) e.1.2
  have hnu := Kpi_le_KnG (ord := ord) e.1.1
  have hlo : (c.lo : ℕ) < k := c.lo.isLt
  have hhi : (c.hi : ℕ) < k := c.hi.isLt
  rw [hsA, hdA, hsB, hdB, hcolo, hcohi] at hsep
  exact pi_le_of_le_succ (K := k + 2) (by omega) (by omega)

include hfeas in
/-- A `V_l`-side cross-color vertex job scheduled with an edge job belongs to a vertex
at or before the edge job's low endpoint. -/
lemma vertex_lo_le {c : ColorPair k} {w : G.V} (hw : G.color w = c.lo) {e : EJob G}
    (hep : epair e = c)
    (h1 : σ (Sum.inl (w, c.hi)) = some (edgeMachine c))
    (h2 : σ (Sum.inr (Sum.inl e)) = some (edgeMachine c)) :
    ord.π w ≤ ord.π e.1.1 := by
  have hnec : c.hi ≠ G.color w := by rw [hw]; exact fun hc => c.lo_ne_hi hc.symm
  have hne : (Sum.inl (w, c.hi) : Job G) ≠ Sum.inr (Sum.inl e) := by simp
  have hsep := sep_of_same_machine hfeas hne h1 h2
  have hcolo : G.color e.1.1 = c.lo := congrArg ColorPair.lo hep
  have hcohi : G.color e.1.2 = c.hi := congrArg ColorPair.hi hep
  have hwlt : ord.π w < ord.π e.1.2 := by
    refine ord.π_mono _ _ ?_
    rw [hw, hcohi]
    exact c.lo_lt_hi
  have hstepw : (k + 2) * ord.π w + (k + 2) ≤ (k + 2) * ord.π e.1.2 := by
    have h3 : ord.π w + 1 ≤ ord.π e.1.2 := hwlt
    calc (k + 2) * ord.π w + (k + 2) = (k + 2) * (ord.π w + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
      _ ≤ (k + 2) * ord.π e.1.2 := Nat.mul_le_mul le_rfl h3
  have hsA : (isem G ord).start (Sum.inl (w, c.hi))
      = (k + 2) * ord.π w - (c.hi : ℕ) - 1 := start_vertex_other hnec
  have hdA : (isem G ord).d (Sum.inl (w, c.hi))
      = (k + 2) * ord.π w - (c.hi : ℕ) := vD_other G ord hnec
  have hsB : (isem G ord).start (Sum.inr (Sum.inl e))
      = (k + 2) * ord.π e.1.1 - (G.color e.1.2 : ℕ) := start_edge e
  have hdB : (isem G ord).d (Sum.inr (Sum.inl e))
      = (k + 2) * ord.π e.1.2 - (G.color e.1.1 : ℕ) - 1 := rfl
  have hKw := K_le_Kpi (ord := ord) w
  have hKu := K_le_Kpi (ord := ord) e.1.1
  have hlo : (c.lo : ℕ) < k := c.lo.isLt
  have hhi : (c.hi : ℕ) < k := c.hi.isLt
  rw [hsA, hdA, hsB, hdB, hcolo, hcohi] at hsep
  exact pi_le_of_le_succ (K := k + 2) (by omega) (by omega)

include hfeas in
/-- A `V_l'`-side cross-color vertex job scheduled with an edge job belongs to a
vertex at or after the edge job's high endpoint. -/
lemma vertex_hi_ge {c : ColorPair k} {w : G.V} (hw : G.color w = c.hi) {e : EJob G}
    (hep : epair e = c)
    (h1 : σ (Sum.inl (w, c.lo)) = some (edgeMachine c))
    (h2 : σ (Sum.inr (Sum.inl e)) = some (edgeMachine c)) :
    ord.π e.1.2 ≤ ord.π w := by
  have hnec : c.lo ≠ G.color w := by rw [hw]; exact c.lo_ne_hi
  have hne : (Sum.inl (w, c.lo) : Job G) ≠ Sum.inr (Sum.inl e) := by simp
  have hsep := sep_of_same_machine hfeas hne h1 h2
  have hcolo : G.color e.1.1 = c.lo := congrArg ColorPair.lo hep
  have hcohi : G.color e.1.2 = c.hi := congrArg ColorPair.hi hep
  have hwgt : ord.π e.1.1 < ord.π w := by
    refine ord.π_mono _ _ ?_
    rw [hw, hcolo]
    exact c.lo_lt_hi
  have hstepw : (k + 2) * ord.π e.1.1 + (k + 2) ≤ (k + 2) * ord.π w := by
    have h3 : ord.π e.1.1 + 1 ≤ ord.π w := hwgt
    calc (k + 2) * ord.π e.1.1 + (k + 2) = (k + 2) * (ord.π e.1.1 + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
      _ ≤ (k + 2) * ord.π w := Nat.mul_le_mul le_rfl h3
  have hsA : (isem G ord).start (Sum.inl (w, c.lo))
      = (k + 2) * ord.π w - (c.lo : ℕ) - 1 := start_vertex_other hnec
  have hdA : (isem G ord).d (Sum.inl (w, c.lo))
      = (k + 2) * ord.π w - (c.lo : ℕ) := vD_other G ord hnec
  have hsB : (isem G ord).start (Sum.inr (Sum.inl e))
      = (k + 2) * ord.π e.1.1 - (G.color e.1.2 : ℕ) := start_edge e
  have hdB : (isem G ord).d (Sum.inr (Sum.inl e))
      = (k + 2) * ord.π e.1.2 - (G.color e.1.1 : ℕ) - 1 := rfl
  have hKw := K_le_Kpi (ord := ord) w
  have hKv := K_le_Kpi (ord := ord) e.1.2
  have hlo : (c.lo : ℕ) < k := c.lo.isLt
  have hhi : (c.hi : ℕ) < k := c.hi.isLt
  rw [hsA, hdA, hsB, hdB, hcolo, hcohi] at hsep
  exact pi_le_of_le_succ (K := k + 2) (by omega) (by omega)

include hfeas in
/-- A `V_l`-side cross-color vertex job scheduled with a `V_l`-side combination job
sits after it. -/
lemma vertex_ge_comb_lo {c : ColorPair k} {w z : G.V} (hw : G.color w = c.lo)
    {hz : G.color z = c.lo}
    (h1 : σ (Sum.inl (w, c.hi)) = some (edgeMachine c))
    (h2 : σ (Sum.inr (Sum.inr ⟨(c, z), Or.inl hz⟩)) = some (edgeMachine c)) :
    ord.π z ≤ ord.π w := by
  have hnec : c.hi ≠ G.color w := by rw [hw]; exact fun hc => c.lo_ne_hi hc.symm
  have hne : (Sum.inl (w, c.hi) : Job G) ≠ Sum.inr (Sum.inr ⟨(c, z), Or.inl hz⟩) := by simp
  have hsep := sep_of_same_machine hfeas hne h1 h2
  have hsA : (isem G ord).start (Sum.inl (w, c.hi))
      = (k + 2) * ord.π w - (c.hi : ℕ) - 1 := start_vertex_other hnec
  have hdA : (isem G ord).d (Sum.inl (w, c.hi))
      = (k + 2) * ord.π w - (c.hi : ℕ) := vD_other G ord hnec
  have hsB : (isem G ord).start (Sum.inr (Sum.inr ⟨(c, z), Or.inl hz⟩)) = 1 :=
    start_comb_lo _ hz
  have hdB : (isem G ord).d (Sum.inr (Sum.inr ⟨(c, z), Or.inl hz⟩))
      = (k + 2) * ord.π z - (c.hi : ℕ) - 1 := cD_lo G ord _ hz
  have hKw := K_le_Kpi (ord := ord) w
  have hKz := K_le_Kpi (ord := ord) z
  have hhi : (c.hi : ℕ) < k := c.hi.isLt
  rw [hsA, hdA, hsB, hdB] at hsep
  exact pi_le_of_le_succ (K := k + 2) (by omega) (by omega)

include hfeas in
/-- A `V_l'`-side cross-color vertex job scheduled with a `V_l'`-side combination
job sits before it. -/
lemma vertex_le_comb_hi {c : ColorPair k} {w z : G.V} (hw : G.color w = c.hi)
    {hz : G.color z = c.hi}
    (h1 : σ (Sum.inl (w, c.lo)) = some (edgeMachine c))
    (h2 : σ (Sum.inr (Sum.inr ⟨(c, z), Or.inr hz⟩)) = some (edgeMachine c)) :
    ord.π w ≤ ord.π z := by
  have hnec : c.lo ≠ G.color w := by rw [hw]; exact c.lo_ne_hi
  have hnelohi : ¬ G.color z = c.lo := by rw [hz]; exact fun hc => c.lo_ne_hi hc.symm
  have hne : (Sum.inl (w, c.lo) : Job G) ≠ Sum.inr (Sum.inr ⟨(c, z), Or.inr hz⟩) := by simp
  have hsep := sep_of_same_machine hfeas hne h1 h2
  have hsA : (isem G ord).start (Sum.inl (w, c.lo))
      = (k + 2) * ord.π w - (c.lo : ℕ) - 1 := start_vertex_other hnec
  have hdA : (isem G ord).d (Sum.inl (w, c.lo))
      = (k + 2) * ord.π w - (c.lo : ℕ) := vD_other G ord hnec
  have hsB : (isem G ord).start (Sum.inr (Sum.inr ⟨(c, z), Or.inr hz⟩))
      = (k + 2) * ord.π z - (c.lo : ℕ) := start_comb_hi _ hnelohi
  have hdB : (isem G ord).d (Sum.inr (Sum.inr ⟨(c, z), Or.inr hz⟩))
      = (k + 2) * nG G + 2 := cD_hi G ord _ hnelohi
  have hKw := K_le_Kpi (ord := ord) w
  have hKz := K_le_Kpi (ord := ord) z
  have hnw := Kpi_le_KnG (ord := ord) w
  have hlo : (c.lo : ℕ) < k := c.lo.isLt
  rw [hsA, hdA, hsB, hdB] at hsep
  exact pi_le_of_le_succ (K := k + 2) (by omega) (by omega)

end Lemma2

/-! ### 4.4 Lemma 2 — weight accounting

Each edge selection machine has exactly two combination-job "slots" (the `V_l`-side
jobs all start at `1`, the `V_l'`-side jobs all end at `(k+2)n_G+2`, so each family is
pairwise conflicting). Bounding the two slots against the machine's edge job gives
`edge + comb weight ≤ c₃ + n_G·c₂` per machine, which is the heart of Lemma 2. -/

section Lemma2Weight

variable {G ord} {σ : (isem G ord).Schedule} (hfeas : (isem G ord).Feasible σ)

include hfeas in
lemma combJob_machine {x : CJob G} {i : Machine k}
    (h : σ (Sum.inr (Sum.inr x)) = some i) : i = edgeMachine x.1.1 :=
  Finset.mem_singleton.mp (hfeas.1 _ _ h)

include hfeas in
/-- Which of the two combination-job slots of an edge selection machine `x` occupies. -/
def sideOf (x : CJob G) : ColorPair k ⊕ ColorPair k :=
  if G.color x.1.2 = x.1.1.lo then Sum.inl x.1.1 else Sum.inr x.1.1

include hfeas in
/-- Two scheduled combination jobs in the same slot of the same machine coincide. -/
lemma comb_slot_unique {x x' : CJob G}
    (h1 : σ (Sum.inr (Sum.inr x)) = some (edgeMachine x.1.1))
    (h2 : σ (Sum.inr (Sum.inr x')) = some (edgeMachine x'.1.1))
    (hs : sideOf x = sideOf x') : x = x' := by
  by_contra hne
  have hjne : (Sum.inr (Sum.inr x) : Job G) ≠ Sum.inr (Sum.inr x') := by simp [hne]
  have hKx := K_le_Kpi (ord := ord) x.1.2
  have hKx' := K_le_Kpi (ord := ord) x'.1.2
  have hnx := Kpi_le_KnG (ord := ord) x.1.2
  have hnx' := Kpi_le_KnG (ord := ord) x'.1.2
  have hhi : (x.1.1.hi : ℕ) < k := x.1.1.hi.isLt
  have hhi' : (x'.1.1.hi : ℕ) < k := x'.1.1.hi.isLt
  have hlolt : (x.1.1.lo : ℕ) < k := x.1.1.lo.isLt
  have hlolt' : (x'.1.1.lo : ℕ) < k := x'.1.1.lo.isLt
  by_cases hlo : G.color x.1.2 = x.1.1.lo
  · have hlo' : G.color x'.1.2 = x'.1.1.lo := by
      by_contra hc
      simp only [sideOf, if_pos hlo, if_neg hc] at hs
      simp at hs
    have hcc : x.1.1 = x'.1.1 := by
      simp only [sideOf, if_pos hlo, if_pos hlo'] at hs
      exact Sum.inl.inj hs
    have hsA : (isem G ord).start (Sum.inr (Sum.inr x)) = 1 := start_comb_lo _ hlo
    have hsA' : (isem G ord).start (Sum.inr (Sum.inr x')) = 1 := start_comb_lo _ hlo'
    have hdA : (isem G ord).d (Sum.inr (Sum.inr x))
        = (k + 2) * ord.π x.1.2 - (x.1.1.hi : ℕ) - 1 := cD_lo G ord _ hlo
    have hdA' : (isem G ord).d (Sum.inr (Sum.inr x'))
        = (k + 2) * ord.π x'.1.2 - (x'.1.1.hi : ℕ) - 1 := cD_lo G ord _ hlo'
    refine hfeas.2 _ _ (edgeMachine x.1.1) hjne ⟨?_, ?_⟩ h1 (by rw [hcc]; exact h2)
    · rw [hsA, hdA']; omega
    · rw [hsA', hdA]; omega
  · have hlo' : ¬ G.color x'.1.2 = x'.1.1.lo := by
      intro hc
      simp only [sideOf, if_neg hlo, if_pos hc] at hs
      simp at hs
    have hcc : x.1.1 = x'.1.1 := by
      simp only [sideOf, if_neg hlo, if_neg hlo'] at hs
      exact Sum.inr.inj hs
    have hsA : (isem G ord).start (Sum.inr (Sum.inr x))
        = (k + 2) * ord.π x.1.2 - (x.1.1.lo : ℕ) := start_comb_hi _ hlo
    have hsA' : (isem G ord).start (Sum.inr (Sum.inr x'))
        = (k + 2) * ord.π x'.1.2 - (x'.1.1.lo : ℕ) := start_comb_hi _ hlo'
    have hdA : (isem G ord).d (Sum.inr (Sum.inr x)) = (k + 2) * nG G + 2 := cD_hi G ord _ hlo
    have hdA' : (isem G ord).d (Sum.inr (Sum.inr x')) = (k + 2) * nG G + 2 := cD_hi G ord _ hlo'
    refine hfeas.2 _ _ (edgeMachine x.1.1) hjne ⟨?_, ?_⟩ h1 (by rw [hcc]; exact h2)
    · rw [hsA, hdA']; omega
    · rw [hsA', hdA]; omega

variable {E : ColorPair k → EJob G}
  (hE : ∀ c, σ (Sum.inr (Sum.inl (E c))) = some (edgeMachine c))

include hfeas hE in
lemma epair_E (c : ColorPair k) : epair (E c) = c :=
  edgeMachine_inj (edgeJob_machine hfeas (hE c)).symm

/-- The per-slot weight cap: the `V_l` slot of machine `c` cannot beat `c₂·π(u_c)`,
and the `V_l'` slot cannot beat `c₂·(n_G − π(v_c))`. -/
def slotBound (E : ColorPair k → EJob G) : ColorPair k ⊕ ColorPair k → ℕ
  | Sum.inl c => c2 G * ord.π (E c).1.1
  | Sum.inr c => c2 G * (nG G - ord.π (E c).1.2)

include hfeas hE in
lemma cW_le_slotBound {x : CJob G} (hx : σ (Sum.inr (Sum.inr x)) = some (edgeMachine x.1.1)) :
    cW G ord x ≤ slotBound (ord := ord) E (sideOf x) := by
  by_cases hlo : G.color x.1.2 = x.1.1.lo
  · have hpi : ord.π x.1.2 ≤ ord.π (E x.1.1).1.1 := by
      refine comb_lo_le (hz := hlo) hfeas (epair_E hfeas hE x.1.1) ?_ (hE x.1.1)
      exact hx
    simp only [sideOf, if_pos hlo, slotBound]
    rw [cW_lo G ord _ hlo]
    exact Nat.mul_le_mul le_rfl hpi
  · have hpi : ord.π (E x.1.1).1.2 ≤ ord.π x.1.2 := by
      have hhi : G.color x.1.2 = x.1.1.hi := x.2.resolve_left hlo
      refine comb_hi_ge (hz := hhi) hfeas (epair_E hfeas hE x.1.1) ?_ (hE x.1.1)
      exact hx
    simp only [sideOf, if_neg hlo, slotBound]
    rw [cW_hi G ord _ hlo]
    exact Nat.mul_le_mul le_rfl (by omega)

include hfeas in
/-- The total weight of scheduled combination jobs is at most the sum of any valid
per-slot bound. -/
lemma comb_sum_le_of_bound (B : ColorPair k ⊕ ColorPair k → ℕ)
    (hB : ∀ x : CJob G, σ (Sum.inr (Sum.inr x)) = some (edgeMachine x.1.1) →
      cW G ord x ≤ B (sideOf x)) :
    (∑ x : CJob G, (σ (Sum.inr (Sum.inr x))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inr x))))
      ≤ ∑ y : ColorPair k ⊕ ColorPair k, B y := by
  classical
  set T : Finset (CJob G) :=
    Finset.univ.filter (fun x => (σ (Sum.inr (Sum.inr x))).isSome = true) with hTdef
  have hmemT : ∀ x : CJob G, x ∈ T ↔ (σ (Sum.inr (Sum.inr x))).isSome = true := by
    intro x; rw [hTdef]; simp
  have hsched : ∀ x ∈ T, σ (Sum.inr (Sum.inr x)) = some (edgeMachine x.1.1) := by
    intro x hx
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp ((hmemT x).mp hx)
    rw [combJob_machine hfeas hi] at hi
    exact hi
  have hz : ∀ x ∈ (Finset.univ : Finset (CJob G)), x ∉ T →
      (σ (Sum.inr (Sum.inr x))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inr x))) = 0 := by
    intro x _ hx
    rw [hmemT] at hx
    cases h : σ (Sum.inr (Sum.inr x))
    · rfl
    · rw [h] at hx; simp at hx
  have hinj : ∀ x ∈ T, ∀ x' ∈ T, sideOf x = sideOf x' → x = x' :=
    fun x hx x' hx' hs => comb_slot_unique hfeas (hsched x hx) (hsched x' hx') hs
  rw [← Finset.sum_subset (Finset.subset_univ T) hz]
  calc (∑ x ∈ T, (σ (Sum.inr (Sum.inr x))).elim 0
          (fun _ => (isem G ord).w (Sum.inr (Sum.inr x))))
      ≤ ∑ x ∈ T, B (sideOf x) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [hsched x hx]
        exact hB x (hsched x hx)
    _ = ∑ y ∈ T.image sideOf, B y := (Finset.sum_image hinj).symm
    _ ≤ ∑ y : ColorPair k ⊕ ColorPair k, B y :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

include hfeas hE in
lemma comb_sum_le_slotBounds :
    (∑ x : CJob G, (σ (Sum.inr (Sum.inr x))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inr x))))
      ≤ ∑ y : ColorPair k ⊕ ColorPair k, slotBound (ord := ord) E y :=
  comb_sum_le_of_bound hfeas _ (fun _ hx => cW_le_slotBound hfeas hE hx)

end Lemma2Weight

/-! ### 4.5 Lemma 2 — the master inequality

`weight σ ≤ (bound on vertex jobs) + C(k,2)·(c₃ + n_G·c₂)`, with the second summand
split as `Σ_c eW(E c) + Σ_slots B`. Every subsequent step instantiates this with a
sharpened `B` or vertex bound and reads off a contradiction. -/

section Lemma2Master

variable {G ord} {σ : (isem G ord).Schedule} (hfeas : (isem G ord).Feasible σ)
variable {E : ColorPair k → EJob G}
  (hE : ∀ c, σ (Sum.inr (Sum.inl (E c))) = some (edgeMachine c))
  (hEu : ∀ c y, σ (Sum.inr (Sum.inl y)) = some (edgeMachine c) → y = E c)

include hfeas hE in
lemma E_injective : Function.Injective E := by
  intro c c' h
  rw [← epair_E hfeas hE c, ← epair_E hfeas hE c', h]

include hfeas hE hEu in
/-- The scheduled edge jobs are exactly the `E c`, one per color combination. -/
lemma edge_sum_eq :
    (∑ e : EJob G, (σ (Sum.inr (Sum.inl e))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inl e))))
      = ∑ c : ColorPair k, eW G ord (E c) := by
  classical
  set S : Finset (EJob G) :=
    Finset.univ.filter (fun e => (σ (Sum.inr (Sum.inl e))).isSome = true) with hSdef
  have hmemS : ∀ e : EJob G, e ∈ S ↔ (σ (Sum.inr (Sum.inl e))).isSome = true := by
    intro e; rw [hSdef]; simp
  have hz : ∀ e ∈ (Finset.univ : Finset (EJob G)), e ∉ S →
      (σ (Sum.inr (Sum.inl e))).elim 0
        (fun _ => (isem G ord).w (Sum.inr (Sum.inl e))) = 0 := by
    intro e _ he
    rw [hmemS] at he
    cases h : σ (Sum.inr (Sum.inl e))
    · rfl
    · rw [h] at he; simp at he
  have hSeq : S = Finset.image E Finset.univ := by
    ext e
    constructor
    · intro he
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp ((hmemS e).mp he)
      rw [edgeJob_machine hfeas hi] at hi
      exact Finset.mem_image.mpr ⟨epair e, Finset.mem_univ _, (hEu _ _ hi).symm⟩
    · intro he
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp he
      rw [hmemS, hE c]
      rfl
  rw [← Finset.sum_subset (Finset.subset_univ S) hz, hSeq,
    Finset.sum_image (fun a _ b _ h => E_injective hfeas hE h)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hE c]
  rfl

omit hfeas hE in
/-- Per machine, the edge job together with the two slot caps totals exactly
`c₃ + n_G·c₂`. This is the tightness that makes Lemma 2 work. -/
lemma edge_add_slotBound_sum :
    (∑ c : ColorPair k, eW G ord (E c))
      + (∑ y : ColorPair k ⊕ ColorPair k, slotBound (ord := ord) E y)
      = Nat.choose k 2 * (c3 G + nG G * c2 G) := by
  have hterm : ∀ c : ColorPair k,
      eW G ord (E c) + (slotBound (ord := ord) E (Sum.inl c)
        + slotBound (ord := ord) E (Sum.inr c)) = c3 G + nG G * c2 G := by
    intro c
    have hab : ord.π (E c).1.1 ≤ ord.π (E c).1.2 := le_of_lt (ord.π_mono _ _ (E c).2.1)
    have hb : ord.π (E c).1.2 ≤ nG G := ord.π_le _
    have e1 : c2 G * (ord.π (E c).1.2 - ord.π (E c).1.1) + c2 G * ord.π (E c).1.1
        = c2 G * ord.π (E c).1.2 := by rw [← Nat.mul_add]; congr 1; omega
    have e2 : c2 G * ord.π (E c).1.2 + c2 G * (nG G - ord.π (E c).1.2) = c2 G * nG G := by
      rw [← Nat.mul_add]; congr 1; omega
    have e3 : c2 G * nG G = nG G * c2 G := Nat.mul_comm _ _
    simp only [slotBound, eW]
    omega
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ,
    card_colorPair, smul_eq_mul]

include hfeas hE hEu in
/-- **The master inequality.** -/
lemma weight_le_master (B : ColorPair k ⊕ ColorPair k → ℕ) (VB : ℕ)
    (hB : (∑ x : CJob G, (σ (Sum.inr (Sum.inr x))).elim 0
            (fun _ => (isem G ord).w (Sum.inr (Sum.inr x)))) ≤ ∑ y, B y)
    (hVB : (∑ x : VJob G, (σ (Sum.inl x)).elim 0
            (fun _ => (isem G ord).w (Sum.inl x))) ≤ VB) :
    (isem G ord).weight σ ≤ VB + ((∑ c : ColorPair k, eW G ord (E c)) + ∑ y, B y) := by
  change (∑ j : Job G, (σ j).elim 0 (fun _ => (isem G ord).w j)) ≤ _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, edge_sum_eq hfeas hE hEu]
  exact Nat.add_le_add hVB (Nat.add_le_add le_rfl hB)

end Lemma2Master

/-! ### 4.6 Lemma 2 — Reading Off the Clique -/

section Lemma2Final

variable {G ord} {σ : (isem G ord).Schedule} (hfeas : (isem G ord).Feasible σ)
  (hW : targetWeight G ≤ (isem G ord).weight σ)
variable {E : ColorPair k → EJob G}
  (hE : ∀ c, σ (Sum.inr (Sum.inl (E c))) = some (edgeMachine c))
  (hEu : ∀ c y, σ (Sum.inr (Sum.inl y)) = some (edgeMachine c) → y = E c)

/-- The vertices whose own-color job is scheduled: the candidate clique. -/
def cliqueSet (σ : (isem G ord).Schedule) : Finset G.V :=
  Finset.univ.filter (fun w => (σ (Sum.inl (w, G.color w))).isSome = true)

lemma mem_cliqueSet {w : G.V} :
    w ∈ cliqueSet σ ↔ (σ (Sum.inl (w, G.color w))).isSome = true := by
  rw [cliqueSet]; simp

lemma vsummand_le (x : VJob G) :
    (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x)) ≤ vW G x := by
  cases σ (Sum.inl x) <;> simp

lemma vertexSum_le_total :
    (∑ x : VJob G, (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x)))
      ≤ nG G * (1 + (k - 1) * c1 G) := by
  rw [← totalVertexWeight (G := G)]
  exact Finset.sum_le_sum fun x _ => vsummand_le x

lemma vertexSum_le_cliqueSet :
    (∑ x : VJob G, (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x)))
      ≤ (cliqueSet σ).card + nG G * ((k - 1) * c1 G) := by
  rw [Fintype.sum_prod_type]
  have hv : ∀ v : G.V,
      (∑ ℓ : Fin k, (σ (Sum.inl (v, ℓ))).elim 0 (fun _ => (isem G ord).w (Sum.inl (v, ℓ))))
        ≤ (if (σ (Sum.inl (v, G.color v))).isSome = true then 1 else 0) + (k - 1) * c1 G := by
    intro v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (G.color v))]
    refine Nat.add_le_add (le_of_eq ?_) ?_
    · cases σ (Sum.inl (v, G.color v)) <;> simp
    · have hb : ∀ ℓ ∈ Finset.univ.erase (G.color v),
          (σ (Sum.inl (v, ℓ))).elim 0 (fun _ => (isem G ord).w (Sum.inl (v, ℓ))) ≤ c1 G :=
        fun ℓ hℓ => le_trans (vsummand_le (v, ℓ))
          (le_of_eq (vW_other G (Finset.ne_of_mem_erase hℓ)))
      refine le_trans (Finset.sum_le_sum (g := fun _ => c1 G) hb) (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
  refine le_trans (Finset.sum_le_sum (fun v _ => hv v)) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Finset.sum_boole, Nat.cast_id]
  simp only [cliqueSet, nG]
  exact le_rfl

lemma vertexSum_add_le_total {v : G.V} {ℓ : Fin k} (hne : ℓ ≠ G.color v)
    (h0 : σ (Sum.inl (v, ℓ)) = none) :
    (∑ x : VJob G, (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x))) + c1 G
      ≤ nG G * (1 + (k - 1) * c1 G) := by
  have hsplit : (σ (Sum.inl ((v, ℓ) : VJob G))).elim 0
        (fun _ => (isem G ord).w (Sum.inl ((v, ℓ) : VJob G)))
      + (∑ x ∈ Finset.univ.erase ((v, ℓ) : VJob G),
          (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x)))
      = ∑ x : VJob G, (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x)) :=
    Finset.add_sum_erase Finset.univ
      (fun x : VJob G => (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x)))
      (Finset.mem_univ _)
  have hsplit2 : vW G ((v, ℓ) : VJob G)
      + (∑ x ∈ Finset.univ.erase ((v, ℓ) : VJob G), vW G x)
      = ∑ x : VJob G, vW G x :=
    Finset.add_sum_erase Finset.univ (fun x : VJob G => vW G x) (Finset.mem_univ _)
  have hz : (σ (Sum.inl ((v, ℓ) : VJob G))).elim 0
      (fun _ => (isem G ord).w (Sum.inl ((v, ℓ) : VJob G))) = 0 := by rw [h0]; rfl
  have hle : (∑ x ∈ Finset.univ.erase ((v, ℓ) : VJob G),
        (σ (Sum.inl x)).elim 0 (fun _ => (isem G ord).w (Sum.inl x)))
      ≤ ∑ x ∈ Finset.univ.erase ((v, ℓ) : VJob G), vW G x :=
    Finset.sum_le_sum fun x _ => vsummand_le x
  have hvw : vW G ((v, ℓ) : VJob G) = c1 G := vW_other G hne
  have htot := totalVertexWeight (G := G) (k := k)
  omega

/-- The own-color job of a vertex conflicts with each of its cross-color jobs. -/
lemma own_cross_conflict {v : G.V} {ℓ : Fin k} (h : ℓ ≠ G.color v) :
    (isem G ord).Conflict (Sum.inl (v, G.color v)) (Sum.inl (v, ℓ)) := by
  have hK := K_le_Kpi (ord := ord) v
  have hc : (ℓ : ℕ) < k := ℓ.isLt
  constructor
  · rw [start_vertex_own]
    change _ < vD G ord (v, ℓ)
    rw [vD_other G ord h]
    omega
  · rw [start_vertex_other h]
    change _ < vD G ord (v, G.color v)
    rw [vD_own]
    omega

include hfeas hW hE hEu in
/-- Every cross-color vertex job is scheduled: dropping one costs `c₁ = n_G + 1`,
more than the whole slack budget `n_G - k`. -/
lemma cross_scheduled (v : G.V) (ℓ : Fin k) (hne : ℓ ≠ G.color v) :
    (σ (Sum.inl (v, ℓ))).isSome = true := by
  by_contra hns
  have h0 : σ (Sum.inl (v, ℓ)) = none := by
    cases h : σ (Sum.inl (v, ℓ))
    · rfl
    · rw [h] at hns; simp at hns
  have hvs := vertexSum_add_le_total (σ := σ) hne h0
  have hm := weight_le_master hfeas hE hEu (slotBound (ord := ord) E) _
    (comb_sum_le_slotBounds hfeas hE) (le_refl _)
  rw [edge_add_slotBound_sum (E := E)] at hm
  have e1 : Nat.choose k 2 * (c3 G + nG G * c2 G)
      = Nat.choose k 2 * c3 G + Nat.choose k 2 * (nG G * c2 G) := Nat.mul_add _ _ _
  have e2 : (k - 1) * nG G * c1 G = nG G * ((k - 1) * c1 G) := by ring
  have e3 : nG G * (1 + (k - 1) * c1 G) = nG G + nG G * ((k - 1) * c1 G) := by ring
  have e4 : c1 G = nG G + 1 := rfl
  simp only [targetWeight] at hW
  omega

include hfeas hW hE hEu in
/-- At least `k` own-color jobs are scheduled. -/
lemma cliqueSet_card_ge : k ≤ (cliqueSet σ).card := by
  have hm := weight_le_master hfeas hE hEu (slotBound (ord := ord) E) _
    (comb_sum_le_slotBounds hfeas hE) (vertexSum_le_cliqueSet (σ := σ))
  rw [edge_add_slotBound_sum (E := E)] at hm
  have e1 : Nat.choose k 2 * (c3 G + nG G * c2 G)
      = Nat.choose k 2 * c3 G + Nat.choose k 2 * (nG G * c2 G) := Nat.mul_add _ _ _
  have e2 : (k - 1) * nG G * c1 G = nG G * ((k - 1) * c1 G) := by ring
  simp only [targetWeight] at hW
  omega

include hfeas hW hE hEu in
/-- The cross-color job of a clique-set vertex of color `c.lo` is scheduled on the edge
selection machine of `c`: it cannot stay on the validation machine, where it would
conflict with the vertex's own-color job. -/
lemma cross_on_machine_lo {c : ColorPair k} {w : G.V} (hmem : w ∈ cliqueSet σ)
    (hw : G.color w = c.lo) : σ (Sum.inl (w, c.hi)) = some (edgeMachine c) := by
  have hne : c.hi ≠ G.color w := by rw [hw]; exact fun hc => c.lo_ne_hi hc.symm
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (cross_scheduled hfeas hW hE hEu w c.hi hne)
  obtain ⟨i0, hi0⟩ := Option.isSome_iff_exists.mp (mem_cliqueSet.mp hmem)
  have hown : σ (Sum.inl (w, G.color w)) = some (validationMachine k) := by
    have hme : i0 ∈ vElig G (w, G.color w) := hfeas.1 _ _ hi0
    rw [vElig_ownColor] at hme
    rw [Finset.mem_singleton.mp hme] at hi0
    exact hi0
  have hjne : (Sum.inl (w, G.color w) : Job G) ≠ Sum.inl (w, c.hi) := fun hh =>
    hne (congrArg Prod.snd (Sum.inl.inj hh)).symm
  have hnotval : i ≠ validationMachine k := by
    rintro rfl
    exact hfeas.2 _ _ (validationMachine k) hjne (own_cross_conflict hne) hown hi
  cases i with
  | none => exact absurd rfl hnotval
  | some c' =>
    have hme : edgeMachine c' ∈ vElig G (w, c.hi) := hfeas.1 _ _ hi
    rw [mem_vElig_edge] at hme
    dsimp only at hme
    rcases hme with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ColorPair.eq_of (hw ▸ h1 : c.lo = c'.lo) h2] at hi ⊢
      exact hi
    · exfalso
      have : c.hi < c.lo := by
        rw [h2, ← hw, h1]
        exact c'.lo_lt_hi
      exact absurd c.lo_lt_hi (by omega)

include hfeas hW hE hEu in
/-- Same, for a clique-set vertex of color `c.hi`. -/
lemma cross_on_machine_hi {c : ColorPair k} {w : G.V} (hmem : w ∈ cliqueSet σ)
    (hw : G.color w = c.hi) : σ (Sum.inl (w, c.lo)) = some (edgeMachine c) := by
  have hne : c.lo ≠ G.color w := by rw [hw]; exact c.lo_ne_hi
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (cross_scheduled hfeas hW hE hEu w c.lo hne)
  obtain ⟨i0, hi0⟩ := Option.isSome_iff_exists.mp (mem_cliqueSet.mp hmem)
  have hown : σ (Sum.inl (w, G.color w)) = some (validationMachine k) := by
    have hme : i0 ∈ vElig G (w, G.color w) := hfeas.1 _ _ hi0
    rw [vElig_ownColor] at hme
    rw [Finset.mem_singleton.mp hme] at hi0
    exact hi0
  have hjne : (Sum.inl (w, G.color w) : Job G) ≠ Sum.inl (w, c.lo) := fun hh =>
    hne (congrArg Prod.snd (Sum.inl.inj hh)).symm
  have hnotval : i ≠ validationMachine k := by
    rintro rfl
    exact hfeas.2 _ _ (validationMachine k) hjne (own_cross_conflict hne) hown hi
  cases i with
  | none => exact absurd rfl hnotval
  | some c' =>
    have hme : edgeMachine c' ∈ vElig G (w, c.lo) := hfeas.1 _ _ hi
    rw [mem_vElig_edge] at hme
    dsimp only at hme
    rcases hme with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      have : c.hi < c.lo := by
        rw [h2, ← hw, h1]
        exact c'.lo_lt_hi
      exact absurd c.lo_lt_hi (by omega)
    · rw [ColorPair.eq_of h2 (hw ▸ h1 : c.hi = c'.hi)] at hi ⊢
      exact hi

include hfeas hW hE hEu in
/-- **The pinning step.** A clique-set vertex of color `c.lo` *is* the low endpoint of
the edge job on machine `c`. The edge job forces `π(w) ≤ π(u_c)`; sharpening the
`V_l` slot cap from `c₂·π(u_c)` to `c₂·π(w)` would leave a deficiency of at least `c₂`,
which the slack budget `n_G - k < c₂` cannot pay for. -/
lemma cliqueSet_eq_lo {c : ColorPair k} {w : G.V} (hmem : w ∈ cliqueSet σ)
    (hw : G.color w = c.lo) : w = (E c).1.1 := by
  have hcross := cross_on_machine_lo hfeas hW hE hEu hmem hw
  have hle : ord.π w ≤ ord.π (E c).1.1 :=
    vertex_lo_le hfeas hw (epair_E hfeas hE c) hcross (hE c)
  refine ord.π_inj (le_antisymm hle ?_)
  by_contra hcon
  have hlt : ord.π w + 1 ≤ ord.π (E c).1.1 := by omega
  set B : ColorPair k ⊕ ColorPair k → ℕ := fun y =>
    if y = Sum.inl c then c2 G * ord.π w else slotBound (ord := ord) E y with hBdef
  have hBok : ∀ x : CJob G, σ (Sum.inr (Sum.inr x)) = some (edgeMachine x.1.1) →
      cW G ord x ≤ B (sideOf x) := by
    intro x hx
    by_cases hy : sideOf x = Sum.inl c
    · rw [hBdef]
      simp only [hy]
      obtain ⟨⟨cc, z⟩, hz⟩ := x
      have hlo : G.color z = cc.lo := by
        by_contra hc
        simp only [sideOf, if_neg hc] at hy
        simp at hy
      have hcc : cc = c := by
        simp only [sideOf, if_pos hlo] at hy
        exact Sum.inl.inj hy
      subst hcc
      rw [cW_lo G ord _ hlo]
      exact Nat.mul_le_mul le_rfl (vertex_ge_comb_lo hfeas hw (hz := hlo) hcross hx)
    · rw [hBdef]
      simp only [if_neg hy]
      exact cW_le_slotBound hfeas hE hx
  have hm := weight_le_master hfeas hE hEu B _ (comb_sum_le_of_bound hfeas B hBok)
    (vertexSum_le_total (σ := σ))
  have hBsum : (∑ y, B y) + slotBound (ord := ord) E (Sum.inl c)
      = (∑ y : ColorPair k ⊕ ColorPair k, slotBound (ord := ord) E y) + c2 G * ord.π w := by
    have h1 : B (Sum.inl c) + ∑ y ∈ Finset.univ.erase (Sum.inl c), B y = ∑ y, B y :=
      Finset.add_sum_erase Finset.univ B (Finset.mem_univ _)
    have h2 : slotBound (ord := ord) E (Sum.inl c)
        + ∑ y ∈ Finset.univ.erase (Sum.inl c), slotBound (ord := ord) E y
        = ∑ y, slotBound (ord := ord) E y :=
      Finset.add_sum_erase Finset.univ _ (Finset.mem_univ _)
    have h3 : ∑ y ∈ Finset.univ.erase (Sum.inl c), B y
        = ∑ y ∈ Finset.univ.erase (Sum.inl c), slotBound (ord := ord) E y :=
      Finset.sum_congr rfl fun y hy => by
        rw [hBdef]; simp only [if_neg (Finset.ne_of_mem_erase hy)]
    have h4 : B (Sum.inl c) = c2 G * ord.π w := by rw [hBdef]; simp
    omega
  have hslot : slotBound (ord := ord) E (Sum.inl c) = c2 G * ord.π (E c).1.1 := rfl
  have hbig : c2 G * ord.π w + c2 G ≤ c2 G * ord.π (E c).1.1 := by
    have := Nat.mul_le_mul (le_refl (c2 G)) hlt
    rw [Nat.mul_add, Nat.mul_one] at this
    exact this
  have hc2 : nG G < c2 G := by simp only [c2]; omega
  have hsum := edge_add_slotBound_sum (ord := ord) (E := E)
  have e1 : Nat.choose k 2 * (c3 G + nG G * c2 G)
      = Nat.choose k 2 * c3 G + Nat.choose k 2 * (nG G * c2 G) := Nat.mul_add _ _ _
  have e2 : (k - 1) * nG G * c1 G = nG G * ((k - 1) * c1 G) := by ring
  have e3 : nG G * (1 + (k - 1) * c1 G) = nG G + nG G * ((k - 1) * c1 G) := by ring
  simp only [targetWeight] at hW
  omega

include hfeas hW hE hEu in
/-- The mirror image: a clique-set vertex of color `c.hi` is the high endpoint. -/
lemma cliqueSet_eq_hi {c : ColorPair k} {w : G.V} (hmem : w ∈ cliqueSet σ)
    (hw : G.color w = c.hi) : w = (E c).1.2 := by
  have hcross := cross_on_machine_hi hfeas hW hE hEu hmem hw
  have hle : ord.π (E c).1.2 ≤ ord.π w :=
    vertex_hi_ge hfeas hw (epair_E hfeas hE c) hcross (hE c)
  refine ord.π_inj (le_antisymm ?_ hle)
  by_contra hcon
  have hlt : ord.π (E c).1.2 + 1 ≤ ord.π w := by omega
  set B : ColorPair k ⊕ ColorPair k → ℕ := fun y =>
    if y = Sum.inr c then c2 G * (nG G - ord.π w) else slotBound (ord := ord) E y with hBdef
  have hBok : ∀ x : CJob G, σ (Sum.inr (Sum.inr x)) = some (edgeMachine x.1.1) →
      cW G ord x ≤ B (sideOf x) := by
    intro x hx
    by_cases hy : sideOf x = Sum.inr c
    · rw [hBdef]
      simp only [hy]
      obtain ⟨⟨cc, z⟩, hz⟩ := x
      have hnlo : ¬ G.color z = cc.lo := by
        intro hc
        simp only [sideOf, if_pos hc] at hy
        simp at hy
      have hcc : cc = c := by
        simp only [sideOf, if_neg hnlo] at hy
        exact Sum.inr.inj hy
      subst hcc
      have hhi : G.color z = cc.hi := hz.resolve_left hnlo
      rw [cW_hi G ord _ hnlo]
      dsimp only
      have hwz : ord.π w ≤ ord.π z := vertex_le_comb_hi hfeas hw (hz := hhi) hcross hx
      exact Nat.mul_le_mul le_rfl (by omega)
    · rw [hBdef]
      simp only [if_neg hy]
      exact cW_le_slotBound hfeas hE hx
  have hm := weight_le_master hfeas hE hEu B _ (comb_sum_le_of_bound hfeas B hBok)
    (vertexSum_le_total (σ := σ))
  have hBsum : (∑ y, B y) + slotBound (ord := ord) E (Sum.inr c)
      = (∑ y : ColorPair k ⊕ ColorPair k, slotBound (ord := ord) E y)
        + c2 G * (nG G - ord.π w) := by
    have h1 : B (Sum.inr c) + ∑ y ∈ Finset.univ.erase (Sum.inr c), B y = ∑ y, B y :=
      Finset.add_sum_erase Finset.univ B (Finset.mem_univ _)
    have h2 : slotBound (ord := ord) E (Sum.inr c)
        + ∑ y ∈ Finset.univ.erase (Sum.inr c), slotBound (ord := ord) E y
        = ∑ y, slotBound (ord := ord) E y :=
      Finset.add_sum_erase Finset.univ _ (Finset.mem_univ _)
    have h3 : ∑ y ∈ Finset.univ.erase (Sum.inr c), B y
        = ∑ y ∈ Finset.univ.erase (Sum.inr c), slotBound (ord := ord) E y :=
      Finset.sum_congr rfl fun y hy => by
        rw [hBdef]; simp only [if_neg (Finset.ne_of_mem_erase hy)]
    have h4 : B (Sum.inr c) = c2 G * (nG G - ord.π w) := by rw [hBdef]; simp
    omega
  have hslot : slotBound (ord := ord) E (Sum.inr c) = c2 G * (nG G - ord.π (E c).1.2) := rfl
  have hwn : ord.π w ≤ nG G := ord.π_le _
  have hbig : c2 G * (nG G - ord.π w) + c2 G ≤ c2 G * (nG G - ord.π (E c).1.2) := by
    have h5 : (nG G - ord.π w) + 1 ≤ nG G - ord.π (E c).1.2 := by omega
    have := Nat.mul_le_mul (le_refl (c2 G)) h5
    rw [Nat.mul_add, Nat.mul_one] at this
    exact this
  have hc2 : nG G < c2 G := by simp only [c2]; omega
  have hsum := edge_add_slotBound_sum (ord := ord) (E := E)
  have e1 : Nat.choose k 2 * (c3 G + nG G * c2 G)
      = Nat.choose k 2 * c3 G + Nat.choose k 2 * (nG G * c2 G) := Nat.mul_add _ _ _
  have e2 : (k - 1) * nG G * c1 G = nG G * ((k - 1) * c1 G) := by ring
  have e3 : nG G * (1 + (k - 1) * c1 G) = nG G + nG G * ((k - 1) * c1 G) := by ring
  simp only [targetWeight] at hW
  omega

end Lemma2Final

/-- **Lemma 2.** A feasible schedule of total weight at least `W` yields a multicolored
clique of size `k`. -/
theorem lemma2 (hweight : (isem G ord).HasWeight (targetWeight G)) : G.HasClique := by
  obtain ⟨σ, hfeas, hW⟩ := hweight
  rcases Nat.lt_or_ge k 1 with hk0 | hk1
  · have hk : k = 0 := by omega
    subst hk
    exact ⟨Fin.elim0, fun c => Fin.elim0 c, fun c _ _ => Fin.elim0 c⟩
  have hnev : Nonempty G.V := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hw0 : (isem G ord).weight σ = 0 := by
      change (∑ j : Job G, _) = 0
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases j with ⟨v, _⟩ | ⟨⟨u, _⟩, _⟩ | ⟨⟨_, z⟩, _⟩
      · exact (hemp.false v).elim
      · exact (hemp.false u).elim
      · exact (hemp.false z).elim
    rw [hw0] at hW
    simp only [targetWeight] at hW
    omega
  rcases Nat.lt_or_ge k 2 with hk | hk2
  · have hk1' : k = 1 := by omega
    subst hk1'
    obtain ⟨v⟩ := hnev
    have hone : ∀ a b : Fin 1, a = b := by
      intro a b
      have ha := a.isLt
      have hb := b.isLt
      exact Fin.ext (by omega)
    exact ⟨fun _ => v, fun c => hone _ _, fun c c' h => absurd (hone c c') h⟩
  -- Main case `k ≥ 2`.
  choose E hE hEu using observation3 G ord σ hfeas hW
  -- Each color contributes at most one vertex to the clique set.
  have hfib : ∀ ℓ : Fin k, ((cliqueSet σ).filter (fun w => G.color w = ℓ)).card ≤ 1 := by
    intro ℓ
    obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin k, ℓ ≠ ℓ' := by
      have h1k : 1 < k := hk2
      by_cases h0 : (ℓ : ℕ) = 0
      · refine ⟨⟨1, h1k⟩, fun hc => ?_⟩
        have hv : (ℓ : ℕ) = 1 := by rw [hc]
        omega
      · refine ⟨⟨0, by omega⟩, fun hc => ?_⟩
        have hv : (ℓ : ℕ) = 0 := by rw [hc]
        omega
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    rcases mkPair_spec hℓ' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : a = (E (mkPair hℓ')).1.1 :=
        cliqueSet_eq_lo hfeas hW hE hEu ha.1 (by rw [ha.2, h1])
      have e2 : b = (E (mkPair hℓ')).1.1 :=
        cliqueSet_eq_lo hfeas hW hE hEu hb.1 (by rw [hb.2, h1])
      rw [e1, e2]
    · have e1 : a = (E (mkPair hℓ')).1.2 :=
        cliqueSet_eq_hi hfeas hW hE hEu ha.1 (by rw [ha.2, h2])
      have e2 : b = (E (mkPair hℓ')).1.2 :=
        cliqueSet_eq_hi hfeas hW hE hEu hb.1 (by rw [hb.2, h2])
      rw [e1, e2]
  -- and there are at least `k` of them, so exactly one per color.
  have hcard : (cliqueSet σ).card
      = ∑ ℓ : Fin k, ((cliqueSet σ).filter (fun w => G.color w = ℓ)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  have hge := cliqueSet_card_ge hfeas hW hE hEu
  have hle : (∑ ℓ : Fin k, ((cliqueSet σ).filter (fun w => G.color w = ℓ)).card)
      ≤ ∑ _ℓ : Fin k, 1 := Finset.sum_le_sum (fun ℓ _ => hfib ℓ)
  have hk_eq : (∑ _ℓ : Fin k, (1 : ℕ)) = k := by simp
  have heq : (∑ ℓ : Fin k, ((cliqueSet σ).filter (fun w => G.color w = ℓ)).card)
      = ∑ _ℓ : Fin k, 1 := le_antisymm hle (by rw [hk_eq, ← hcard]; exact hge)
  have hone : ∀ ℓ : Fin k, ((cliqueSet σ).filter (fun w => G.color w = ℓ)).card = 1 :=
    fun ℓ => (Finset.sum_eq_sum_iff_of_le (fun i _ => hfib i)).mp heq ℓ (Finset.mem_univ ℓ)
  have hsing : ∀ ℓ : Fin k, ∃ w : G.V,
      (cliqueSet σ).filter (fun w => G.color w = ℓ) = {w} :=
    fun ℓ => Finset.card_eq_one.mp (hone ℓ)
  choose fv hfv using hsing
  have hfvmem : ∀ ℓ, fv ℓ ∈ cliqueSet σ ∧ G.color (fv ℓ) = ℓ := by
    intro ℓ
    have h : fv ℓ ∈ (cliqueSet σ).filter (fun w => G.color w = ℓ) := by
      rw [hfv ℓ]; exact Finset.mem_singleton_self _
    simpa using h
  refine ⟨fv, fun ℓ => (hfvmem ℓ).2, fun ℓ ℓ' hne' => ?_⟩
  rcases mkPair_spec hne' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : fv ℓ = (E (mkPair hne')).1.1 :=
      cliqueSet_eq_lo hfeas hW hE hEu (hfvmem ℓ).1 (by rw [(hfvmem ℓ).2, h1])
    have e2 : fv ℓ' = (E (mkPair hne')).1.2 :=
      cliqueSet_eq_hi hfeas hW hE hEu (hfvmem ℓ').1 (by rw [(hfvmem ℓ').2, h2])
    rw [e1, e2]
    exact (E (mkPair hne')).2.2
  · have e1 : fv ℓ = (E (mkPair hne')).1.2 :=
      cliqueSet_eq_hi hfeas hW hE hEu (hfvmem ℓ).1 (by rw [(hfvmem ℓ).2, h2])
    have e2 : fv ℓ' = (E (mkPair hne')).1.1 :=
      cliqueSet_eq_lo hfeas hW hE hEu (hfvmem ℓ').1 (by rw [(hfvmem ℓ').2, h1])
    rw [e1, e2]
    exact G.E_symm _ _ (E (mkPair hne')).2.2

/-- **Theorem 1 (correctness of Construction 1).** `G` has a multicolored clique of
size `k` iff the constructed instance admits a feasible schedule of weight at least `W`.

The constructed instance has `C(k,2) + 1` machines (`card_machine`), a function of the
parameter `k` alone, so this is the parameterized reduction establishing W[1]-hardness
for `m`. -/
theorem theorem1_correctness :
    G.HasClique ↔ (isem G ord).HasWeight (targetWeight G) :=
  ⟨lemma1 G ord, lemma2 G ord⟩

end Construction1

end Lax470956Proofs.Construction1Typed
