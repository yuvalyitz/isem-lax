import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic
import Mathlib.Data.List.GetD

/-!
Reading a length-prefixed word into an array, as an IMP+ command with its specification.

The polynomial-time predicate hands a program its input preceded by its length. Every
program written against it begins the same way: read the length, then copy that many
entries into an array so that they can be read again. This file is that beginning, stated
once for any bound on the values.
-/

namespace Lax470956Proofs.ReadAll

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

def readBody : Com :=
  .seq (.read "rv") (.seq (.store "a" (V "rt") (V "rv")) (bump "rt"))

def readLoop : Com := .seq (.assign "rt" (.lit 0)) (.while (.lt (V "rt") (V "L")) readBody)

/-- Read the length, then the word. -/
def readAll : Com := .seq (.read "L") readLoop

variable {B : ℕ} {y : List ℕ}

def RInv (y : List ℕ) (σ : Env) : Prop :=
  σ.vars "L" = y.length ∧ σ.vars "rt" ≤ y.length ∧ (σ.arrs "a").length = y.length ∧
    (∀ i < σ.vars "rt", (σ.arrs "a").getD i 0 = y.getD i 0) ∧
    σ.inp = y.drop (σ.vars "rt") ∧ σ.out = []

theorem readBody_spec (hy : ∀ v ∈ y, v < B) (hL : y.length + 1 < B) :
    Spec B (fun σ => RInv y σ ∧ σ.vars "rt" < y.length) readBody
      (fun σ σ' => RInv y σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 8 := by
  refine Spec.pre (P := fun σ => RInv y σ ∧ σ.vars "rt" < y.length ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < B ∧ σ.vars "rt" < (σ.arrs "a").length) ?_ ?_
  · run_vcg
    · obtain ⟨hLv, hle, hlen, hcell, hinp, hout⟩ := ‹RInv y σ›
      have htlt := ‹σ.vars "rt" < y.length›
      have hidx : σ.vars "rt" < (σ.arrs "a").length := by rw [hlen]; exact htlt
      simp only [RInv]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hLv
      · exact htlt
      · exact hlen
      · intro i hi
        rcases Nat.lt_or_ge i (σ.vars "rt") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell i h
        · have hie : i = σ.vars "rt" := by omega
          subst hie
          rw [hinp]
          simp [hidx, List.head?_drop]
      · rw [hinp, List.tail_drop]
      · exact hout
    · simp only [Env.setVar]
      exact ‹σ.inp.headD 0 < B›
  · rintro σ ⟨hI, ht⟩
    have hinp : σ.inp = y.drop (σ.vars "rt") := hI.2.2.2.2.1
    have hne : σ.inp ≠ [] := by
      rw [hinp]; intro hc
      have : (y.drop (σ.vars "rt")).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop] at this; omega
    refine ⟨hI, ht, hne, ?_, by rw [hI.2.2.1]; exact ht⟩
    rcases hh : σ.inp with _ | ⟨u, rest⟩
    · exact absurd hh hne
    · have : u ∈ y.drop (σ.vars "rt") := by rw [← hinp, hh]; exact List.mem_cons_self
      exact hy u (List.mem_of_mem_drop this)

theorem readLoop_spec (hy : ∀ v ∈ y, v < B) (hL : y.length + 1 < B) :
    Spec B (fun σ => RInv y (σ.setVar "rt" 0)) readLoop
      (fun _ σ' => RInv y σ' ∧ σ'.vars "rt" = y.length) (12 * y.length + 6) :=
  Spec.forRangeZero "rt" "L" (RInv y) y.length 8 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (readBody_spec hy hL)

/-- **The word has been read**: its length is in `L` and its entries are in `a`. -/
theorem readAll_spec (hy : ∀ v ∈ y, v < B) (hL : y.length + 1 < B) :
    Spec B (fun σ => σ.inp = y.length :: y ∧ σ.out = [] ∧ (σ.arrs "a").length = y.length)
      readAll
      (fun _ σ' => σ'.vars "L" = y.length ∧ σ'.arrs "a" = y ∧ σ'.out = [] ∧ σ'.inp = [])
      (12 * y.length + 10) := by
  run_vcg [readLoop_spec hy hL]
  · obtain ⟨⟨hLv, -, hlen, hcell, hinp, hout⟩, ht⟩ := ‹RInv y _ ∧ _›
    refine ⟨hLv, ?_, hout, by rw [hinp, ht]; simp⟩
    refine List.ext_getElem hlen fun i h1 h2 => ?_
    have := hcell i (by rw [ht]; exact h2)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
      Option.getD_some] at this
  all_goals simp_all [RInv]

end Lax470956Proofs.ReadAll
