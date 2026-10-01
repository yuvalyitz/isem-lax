import Lax470956Proofs.Construction1Prog
import Lax470956Proofs.Pmax

/-!
Construction 1 as a word RAM program: the word, the bound, and the copy loop.
-/

namespace Lax470956Proofs.Construction1Read

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.MulticolouredClique Lax470956.Construction1
open Lax470956Proofs.Construction1Shape Lax470956Proofs.Construction1Prog

variable {x : List ℕ} {G : Instance}

/-! ### The Word -/

/-- The part of the word the program copies: everything after the two counts. -/
def body (x : List ℕ) : List ℕ := x.drop 2

lemma body_getD (x : List ℕ) (i : ℕ) : (body x).getD i 0 = x.getD (2 + i) 0 := by
  simp [body, List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma body_off (x : List ℕ) (i : ℕ) : (body x).getD i 0 = off x i := body_getD x i

lemma body_tgt (x : List ℕ) (t : ℕ) : (body x).getD (vn x + 1 + t) 0 = tgt x t := by
  rw [body_getD, tgt]; congr 1; omega

lemma body_col (x : List ℕ) (v : ℕ) :
    (body x).getD (vn x + 1 + 2 * ve x + v) 0 = colr x v := by
  rw [body_getD, colr]; congr 1; omega

lemma body_length (hR : Reads x G) : (body x).length = 2 * vn x + 2 * ve x + 2 := by
  have := hR.length_eq
  simp only [body, List.length_drop]; omega

lemma head_shape (hR : Reads x G) : x = vn x :: ve x :: body x := by
  have hlen := hR.length_eq
  rcases x with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at hlen; omega
  · simp at hlen; omega
  · rfl

/-! ### The Bound on the Values -/

/-- Every number the program forms is below this: an entry of the word or a count of
them, or an entry of the word it emits or a count of those. -/
noncomputable def bnd (x : List ℕ) (G : Instance) : ℕ :=
  64 * (x.length + x.foldr max 0) + 64 * ((emit G).length + targetWeight G) + 64

lemma entry_lt_bnd {v : ℕ} (hv : v ∈ x) : v < bnd x G := by
  have := Lax470956Proofs.Pmax.le_foldr_max hv
  simp only [bnd]; omega

lemma body_entry_lt (i : ℕ) (hi : i < (body x).length) : (body x).getD i 0 < bnd x G := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact entry_lt_bnd (List.mem_of_mem_drop (List.getElem_mem hi))

lemma len_lt_bnd : 8 * x.length + 8 < bnd x G := by simp only [bnd]; omega

lemma four_nJobs_le : 4 * nJobs G + 4 ≤ (emit G).length := by
  simp [emit, procBlock, dueBlock, wtBlock, offBlock]; omega

lemma nJobs_lt_bnd : 64 * nJobs G + 64 < bnd x G := by
  have := four_nJobs_le (G := G)
  simp only [bnd]; omega

lemma tw_lt_bnd : 64 * targetWeight G + 64 ≤ bnd x G := by simp only [bnd]; omega

lemma kk_lt_bnd (hR : Reads x G) : kk x < bnd x G := by
  have hlen := hR.length_eq
  have hlt : 3 + 2 * vn x + 2 * ve x < x.length := by omega
  refine entry_lt_bnd ?_
  rw [kk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact List.getElem_mem hlt

/-- The counts and the parameter, with room to spare. -/
lemma small_lt_bnd (hR : Reads x G) :
    8 * (vn x + ve x + kk x) + 8 * x.length + 8 < bnd x G := by
  have h1 : vn x ≤ x.foldr max 0 := Lax470956Proofs.Pmax.le_foldr_max (by
    rw [head_shape hR]; exact List.mem_cons_self)
  have h2 : ve x ≤ x.foldr max 0 := Lax470956Proofs.Pmax.le_foldr_max (by
    rw [head_shape hR]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have h3 : kk x ≤ x.foldr max 0 := by
    have hlen := hR.length_eq
    have hlt : 3 + 2 * vn x + 2 * ve x < x.length := by omega
    refine Lax470956Proofs.Pmax.le_foldr_max ?_
    rw [kk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  simp only [bnd]; omega

/-- The one inequality every bound below is read off. -/
lemma master (hR : Reads x G) :
    8 * (vn x + ve x + kk x) + 64 * nJobs G + 64 * targetWeight G + 128 ≤ bnd x G := by
  have h1 : vn x ≤ x.foldr max 0 := Lax470956Proofs.Pmax.le_foldr_max (by
    rw [head_shape hR]; exact List.mem_cons_self)
  have h2 : ve x ≤ x.foldr max 0 := Lax470956Proofs.Pmax.le_foldr_max (by
    rw [head_shape hR]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have h3 : kk x ≤ x.foldr max 0 := by
    have hlen := hR.length_eq
    have hlt : 3 + 2 * vn x + 2 * ve x < x.length := by omega
    refine Lax470956Proofs.Pmax.le_foldr_max ?_
    rw [kk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  have h4 := four_nJobs_le (G := G)
  simp only [bnd]; omega

lemma nk_le_nJobs (hR : Reads x G) : vn x * kk x ≤ nJobs G := by
  rw [hR.vn_eq, hR.kk_eq]; simp only [nJobs, nVJob]; omega

/-! ### The Copy Loop -/

/-- The lengths of the three tables the program fills later. -/
def Tables (x : List ℕ) (σ : Env) : Prop :=
  (σ.arrs "r").length = vn x ∧ (σ.arrs "eu").length = 2 * ve x ∧
    (σ.arrs "ev").length = 2 * ve x

/-- The state of the loop that copies the word into the array. -/
def RInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = vn x ∧ σ.vars "m" = ve x ∧ σ.vars "L" = (body x).length ∧
    σ.vars "t" ≤ (body x).length ∧
    (σ.arrs "a").length = (body x).length ∧
    (∀ i < σ.vars "t", (σ.arrs "a").getD i 0 = (body x).getD i 0) ∧
    σ.inp = (body x).drop (σ.vars "t") ∧ σ.out = [] ∧ Tables x σ

theorem readBody_spec :
    Spec (bnd x G) (fun σ => RInv x σ ∧ σ.vars "t" < (body x).length) readBody
      (fun σ σ' => RInv x σ' ∧ σ'.vars "t" = σ.vars "t" + 1) 8 := by
  refine Spec.pre (P := fun σ => RInv x σ ∧ σ.vars "t" < (body x).length ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < bnd x G ∧ σ.vars "t" < (σ.arrs "a").length ∧
      σ.vars "t" + 1 < bnd x G) ?_ ?_
  · run_vcg
    · obtain ⟨hn, hm, hL, hle, hlen, hcell, hinp, hout, hT⟩ := ‹RInv x σ›
      have htlt := ‹σ.vars "t" < (body x).length›
      have hidx : σ.vars "t" < (σ.arrs "a").length := by rw [hlen]; exact htlt
      simp only [RInv, Tables]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hn
      · exact hm
      · exact hL
      · exact htlt
      · exact hlen
      · intro i hi
        rcases Nat.lt_or_ge i (σ.vars "t") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell i h
        · have hie : i = σ.vars "t" := by omega
          subst hie
          rw [hinp]
          simp [List.getElem?_set, hidx, List.head?_drop]
      · rw [hinp, List.tail_drop]
      · exact hout
      · exact hT
    · simp only [Env.setVar, if_pos rfl]
      exact ‹σ.inp.headD 0 < bnd x G›
  · rintro σ ⟨hI, ht⟩
    have hinp : σ.inp = (body x).drop (σ.vars "t") := hI.2.2.2.2.2.2.1
    have hne : σ.inp ≠ [] := by
      rw [hinp]
      intro hc
      have : ((body x).drop (σ.vars "t")).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop] at this
      omega
    refine ⟨hI, ht, hne, ?_, ?_, ?_⟩
    · rcases hh : σ.inp with _ | ⟨u, rest⟩
      · exact absurd hh hne
      · have hu : u ∈ x := by
          have : u ∈ (body x).drop (σ.vars "t") := by rw [← hinp, hh]; exact List.mem_cons_self
          exact List.mem_of_mem_drop (l := x) (i := 2) (List.mem_of_mem_drop this)
        exact entry_lt_bnd hu
    · rw [hI.2.2.2.2.1]; exact ht
    · have h1 : (body x).length ≤ x.length := by simp [body]
      have := len_lt_bnd (x := x) (G := G)
      omega

/-- The copy loop reads the rest of the word into the array. -/
theorem readLoop_spec :
    Spec (bnd x G) (fun σ => RInv x (σ.setVar "t" 0)) readLoop
      (fun _ σ' => RInv x σ' ∧ σ'.vars "t" = (body x).length)
      (12 * (body x).length + 6) :=
  Spec.forRangeZero "t" "L" (RInv x) (body x).length 8
    (by have h1 : (body x).length ≤ x.length := by simp [body]
        have := len_lt_bnd (x := x) (G := G); omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) readBody_spec

/-- When the copy loop is done the array holds the rest of the word. -/
theorem arr_eq {σ : Env} (h : RInv x σ) (ht : σ.vars "t" = (body x).length) :
    σ.arrs "a" = body x := by
  obtain ⟨-, -, -, -, hlen, hcell, -, -, -⟩ := h
  refine List.ext_getElem hlen ?_
  intro i h1 h2
  have hi := hcell i (by rw [ht]; exact h2)
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at hi

end Lax470956Proofs.Construction1Read
