import Lax470956Proofs.Construction1Ctx

/-!
Construction 1 as a word RAM program: from the input tape to the context of the passes.
-/

namespace Lax470956Proofs.Construction1Setup

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.MulticolouredClique Lax470956.Construction1
open Lax470956Proofs.Construction1Shape Lax470956Proofs.Construction1Prog
open Lax470956Proofs.Construction1Read Lax470956Proofs.Construction1Rank
open Lax470956Proofs.Construction1Edges Lax470956Proofs.Construction1Tables
open Lax470956Proofs.Construction1Ctx

variable {x : List ℕ} {G : Instance}

/-- The word has been copied. -/
def A1 (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = vn x ∧ σ.vars "m" = ve x ∧ σ.arrs "a" = body x ∧ σ.out = [] ∧ Tables x σ

theorem setupA_spec (hR : Reads x G) :
    Spec (bnd x G)
      (fun σ => σ.inp = vn x :: ve x :: body x ∧ σ.out = [] ∧
        (σ.arrs "a").length = (body x).length ∧ Tables x σ ∧ ReadsB x G ∧ Big x G)
      setupA (fun _ σ' => A1 x σ') (12 * (body x).length + 40) := by
  run_vcg [readLoop_spec (x := x) (G := G)]
  all_goals have hinp := ‹σ.inp = vn x :: ve x :: body x›
  all_goals have hout0 := ‹σ.out = []›
  all_goals have halen := ‹(σ.arrs "a").length = (body x).length›
  all_goals obtain ⟨hr, heu, hev⟩ := ‹Tables x σ›
  all_goals obtain ⟨hoffB, htgtB, hcolB, hlenB, hblen⟩ := ‹ReadsB x G›
  all_goals have hbig := ‹Big x G›
  all_goals have hsm := hbig.small
  all_goals have hvn := hbig.vn_eq
  · obtain ⟨hI, ht⟩ := ‹RInv x _ ∧ _›
    exact ⟨hI.1, hI.2.1, arr_eq hI ht, hI.2.2.2.2.2.2.2.1, hI.2.2.2.2.2.2.2.2⟩
  all_goals try simp only [RInv, Tables] at *
  all_goals try simp_all
  all_goals try omega

lemma colr_vn (x : List ℕ) : colr x (vn x) = kk x := by
  rw [colr, kk]; congr 1; omega

/-- The rank table has been filled. -/
def B1 (x : List ℕ) (σ : Env) : Prop := Base x σ ∧ σ.out = [] ∧ Ranked x σ ∧
  (σ.arrs "eu").length = 2 * ve x ∧ (σ.arrs "ev").length = 2 * ve x

theorem setupB_spec (hR : Reads x G) :
    Spec (bnd x G) (fun σ => A1 x σ ∧ ReadsB x G ∧ Big x G)
      setupB (fun _ σ' => B1 x σ') (44 * (vn x * kk x) + 60) := by
  run_vcg [rankLoop_spec hR]
  all_goals obtain ⟨hn, hm, ha, hout, hr, heu, hev⟩ := ‹A1 x σ›
  all_goals obtain ⟨hoffB, htgtB, hcolB, hlenB, hblen⟩ := ‹ReadsB x G›
  all_goals have hbig := ‹Big x G›
  all_goals have hsm := hbig.small
  all_goals have hvn := hbig.vn_eq
  all_goals have hkk := hbig.kk_eq
  all_goals have hnkB := nk_le_nJobs hR
  all_goals have hkB := kk_lt_bnd (G := G) hR
  · obtain ⟨⟨hB, hout', hT, -, -, hrk⟩, hi⟩ := ‹KInv x _ ∧ _›
    refine ⟨hB, hout', ⟨hT.1, fun v hv => hrk v hv ?_⟩, hT.2.1, hT.2.2⟩
    rw [hi]
    have hc : colr x v < kk x := by
      have hv' : v < G.vertices := by omega
      rw [hR.colr_eq ⟨v, hv'⟩, hkk]
      exact (G.colour ⟨v, hv'⟩).isLt
    have h1 : (colr x v + 1) * vn x ≤ kk x * vn x := Nat.mul_le_mul_right _ hc
    rw [Nat.mul_comm (vn x) (kk x)]
    have h2 : (colr x v + 1) * vn x = colr x v * vn x + vn x := by ring
    omega
  all_goals try simp only [KInv, Base, Tables]
  all_goals try simp [hn, hm, ha, hout, hr, heu, hev, body_off', sweep, colr_vn]
  all_goals try omega
  all_goals try (rw [← hvn, ← hkk]; omega)

theorem setupC_spec (hR : Reads x G) :
    Spec (bnd x G) (fun σ => B1 x σ ∧ ReadsB x G ∧ Big x G)
      setupC (fun _ σ' => H0 x σ') (64 * (vn x + 2 * ve x) + 60) := by
  run_vcg [edgeLoop_spec hR]
  all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hout, hrk, heu, hev⟩ := ‹B1 x σ›
  all_goals obtain ⟨hoffB, htgtB, hcolB, hlenB, hblen⟩ := ‹ReadsB x G›
  all_goals have hbig := ‹Big x G›
  all_goals have hsm := hbig.small
  all_goals have hvn := hbig.vn_eq
  · obtain ⟨⟨hB, hout', hrk', hS, hiup, hun, hoff, hp2, hE, heu', hev', htu, htv⟩, hi⟩ :=
      ‹EInv x _ ∧ _›
    have hp := hp2
    have hp' := Nat.le_antisymm hp2 (by omega)
    rw [hp'] at hE htu htv
    exact ⟨hB, hout', hrk', hE, heu', hev', htu, htv⟩
  all_goals try simp only [EInv, Base, Ranked]
  all_goals try simp [hn, hm, ha, htb, hcb, hk, hnk, hout, heu, hev, hR.off_zero]
  all_goals try omega
  all_goals (simpa [Ranked, List.getD_eq_getElem?_getD] using hrk)

/-- The cost of everything before the first write. -/
def setupCost (x : List ℕ) : ℕ :=
  12 * (body x).length + 44 * (vn x * kk x) + 64 * (vn x + 2 * ve x) + 400

/-- **From the input tape to the context of the passes.** -/
theorem setup_spec (hR : Reads x G) :
    Spec (bnd x G)
      (fun σ => σ.inp = vn x :: ve x :: body x ∧ σ.out = [] ∧
        (σ.arrs "a").length = (body x).length ∧ Tables x σ)
      setup (fun _ σ' => Ctx x G σ' ∧ σ'.out = [])
      (12 * (body x).length + 44 * (vn x * kk x) + 64 * (vn x + 2 * ve x) + 400) := by
  have hRB := readsB hR
  have hbig := big hR
  run_vcg [setupA_spec hR, setupB_spec hR, setupC_spec hR, header1_spec (x := x) (G := G),
    header2_spec (x := x) (G := G), header3_spec (x := x) (G := G)]
  all_goals try simp only [setupCost]
  all_goals try omega
  all_goals try assumption
  all_goals try exact ⟨by assumption, hRB, hbig⟩
  all_goals try exact ⟨by assumption, hbig⟩
  all_goals try exact ⟨by assumption, by assumption, by assumption, by assumption, hRB, hbig⟩

end Lax470956Proofs.Construction1Setup
