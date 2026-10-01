import Lax470956Proofs.Construction1Tables

/-!
Construction 1 as a word RAM program: what the passes know, and the header that
establishes it.
-/

namespace Lax470956Proofs.Construction1Ctx

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.MulticolouredClique Lax470956.Construction1
open Lax470956Proofs.Construction1Shape Lax470956Proofs.Construction1Prog
open Lax470956Proofs.Construction1Read Lax470956Proofs.Construction1Rank
open Lax470956Proofs.Construction1Edges Lax470956Proofs.Construction1Tables

variable {x : List ℕ} {G : Instance}

/-- The edge table, filled. -/
def EDone (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "E" = (acc x (2 * ve x)).length ∧
    (σ.arrs "eu").length = 2 * ve x ∧ (σ.arrs "ev").length = 2 * ve x ∧
    (σ.arrs "eu").take (σ.vars "E") = (acc x (2 * ve x)).map Prod.fst ∧
    (σ.arrs "ev").take (σ.vars "E") = (acc x (2 * ve x)).map Prod.snd

/-- **What every pass knows**: the copied word, the two tables, and the constants of the
construction. -/
def Ctx (x : List ℕ) (G : Instance) (σ : Env) : Prop :=
  Base x σ ∧ Ranked x σ ∧ EDone x σ ∧
    σ.vars "K" = G.colours + 2 ∧ σ.vars "c1" = c1 G ∧ σ.vars "c2" = c2 G ∧
    σ.vars "val" = G.colours.choose 2 ∧ σ.vars "M" = nMach G ∧
    σ.vars "nc" = nCJob G ∧ σ.vars "nkc" = nVJob G + nCJob G ∧
    σ.vars "nJ" = nJobs G ∧ σ.vars "N" = nJobs G + 1 ∧
    σ.vars "W" = targetWeight G ∧ (1 < G.colours → σ.vars "c3" = c3 G)

/-- The scalars the context is about. -/
def ctxVars : List String :=
  ["n", "m", "tb", "cb", "k", "nk", "E", "K", "c1", "c2", "c3", "val", "M", "nc", "nkc",
    "nJ", "N", "W"]

/-- A scalar the context does not mention may be assigned freely. -/
theorem Ctx.setVar {σ : Env} (h : Ctx x G σ) (y : String) (v : ℕ) (hy : y ∉ ctxVars) :
    Ctx x G (σ.setVar y v) := by
  simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hy
  simpa [Ctx, Base, Ranked, EDone, Env.setVar, Ne.symm h1, Ne.symm h2, Ne.symm h3,
    Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10,
    Ne.symm h11, Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16,
    Ne.symm h17, Ne.symm h18] using h

/-! ### The Header -/

/-- What the tables leave behind. -/
def H0 (x : List ℕ) (σ : Env) : Prop := Base x σ ∧ σ.out = [] ∧ Ranked x σ ∧ EDone x σ

def H1 (x : List ℕ) (G : Instance) (σ : Env) : Prop :=
  H0 x σ ∧ σ.vars "K" = G.colours + 2 ∧ σ.vars "c1" = c1 G ∧ σ.vars "c2" = c2 G ∧
    σ.vars "val" = G.colours.choose 2

/-- The numeric facts the program's arithmetic stays below the bound by. -/
structure Big (x : List ℕ) (G : Instance) : Prop where
  vn_eq : vn x = G.vertices
  kk_eq : kk x = G.colours
  small : 8 * (G.vertices + ve x + G.colours) + 64 * nJobs G + 64 < bnd x G
  kn1 : (G.colours - 1) * G.vertices < bnd x G
  c2B : (G.colours - 1) * G.vertices * (G.vertices + 1) + G.vertices + 1 + G.colours
    < bnd x G
  w0 : (G.colours - 1) * G.vertices * c1 G + G.colours < bnd x G
  kk1 : G.colours * (G.colours - 1) < bnd x G
  kkB : G.colours * G.colours < bnd x G
  ncB : G.colours * G.colours * G.vertices ≤ nJobs G
  knB : G.colours * G.vertices ≤ nJobs G
  m1 : 1 < G.colours →
    (G.colours * G.vertices + G.colours * G.colours * G.vertices) * G.vertices < bnd x G
  m3 : 1 < G.colours → G.colours.choose 2 * c3 G
    + G.colours.choose 2 * (G.vertices * c2 G)
    + ((G.colours - 1) * G.vertices * c1 G + G.colours) < bnd x G
  m4 : 1 < G.colours → G.vertices * c2 G < bnd x G
  c3B : 1 < G.colours → c3 G < bnd x G
  Kp : ∀ p ≤ G.vertices, (G.colours + 2) * p + G.colours + 4 < bnd x G
  Kd : ∀ p q, p ≤ G.vertices → (G.colours + 2) * (p - q) + 2 * G.colours + 4 < bnd x G
  c2p : 1 < G.colours → ∀ p q, p ≤ G.vertices → c2 G * (p - q) + c3 G < bnd x G
  pe : ∀ b ≤ G.colours, b * (b - 1) + G.colours < bnd x G
  accLen : (acc x (2 * ve x)).length = nEJob G

lemma c3_eq (G : Instance) :
    (G.colours * G.vertices + G.colours * G.colours * G.vertices) * G.vertices * c2 G + 1
      = c3 G := by
  simp only [c3, sq]

lemma two_choose (k : ℕ) : k * (k - 1) = 2 * k.choose 2 := by
  rw [Nat.choose_two_right]
  have h : 2 ∣ k * (k - 1) := (Nat.even_mul_pred_self k).two_dvd
  omega

theorem big (hR : Reads x G) : Big x G := by
  have hm := master hR
  rw [hR.vn_eq, hR.kk_eq] at hm
  have htw : targetWeight G = G.colours.choose 2 * c3 G
      + G.colours.choose 2 * (G.vertices * c2 G)
      + (G.colours - 1) * G.vertices * c1 G + G.colours := rfl
  have hc1 : 1 ≤ c1 G := by simp only [c1]; omega
  have hc2 : 1 ≤ c2 G := by simp only [c2]; omega
  have hc3 : 1 ≤ c3 G := by simp only [c3]; omega
  have hnJ : nJobs G = G.vertices * G.colours + G.colours * G.colours * G.vertices
      + nEJob G := rfl
  have hkn : G.colours * G.vertices = G.vertices * G.colours := Nat.mul_comm _ _
  have hch : G.colours.choose 2 ≤ G.colours.choose 2 * c3 G := Nat.le_mul_of_pos_right _ hc3
  have hkn1 : (G.colours - 1) * G.vertices ≤ (G.colours - 1) * G.vertices * c1 G :=
    Nat.le_mul_of_pos_right _ hc1
  have hc1e : (G.colours - 1) * G.vertices * (G.vertices + 1)
      = (G.colours - 1) * G.vertices * c1 G := rfl
  have h2c := two_choose G.colours
  have hKn : ∀ p ≤ G.vertices, (G.colours + 2) * p ≤ G.colours * G.vertices + 2 * G.vertices := by
    intro p hp
    calc (G.colours + 2) * p ≤ (G.colours + 2) * G.vertices := Nat.mul_le_mul_left _ hp
      _ = G.colours * G.vertices + 2 * G.vertices := by ring
  have hpos : 1 < G.colours → 1 ≤ G.colours.choose 2 := fun h => Nat.choose_pos (by omega)
  have hC3 : 1 < G.colours → c3 G ≤ G.colours.choose 2 * c3 G := fun h =>
    Nat.le_mul_of_pos_left _ (hpos h)
  have hC2 : 1 < G.colours → G.vertices * c2 G ≤ G.colours.choose 2 * (G.vertices * c2 G) :=
    fun h => Nat.le_mul_of_pos_left _ (hpos h)
  refine ⟨hR.vn_eq, hR.kk_eq, by omega, by omega, by omega, by omega, by omega, ?_, by omega,
    by omega, fun h => ?_, fun h => by omega, fun h => by have := hC2 h; omega,
    fun h => by have := hC3 h; omega, fun p hp => by have := hKn p hp; omega,
    fun p q hp => by have := hKn (p - q) (by omega); omega, fun h p q hp => ?_,
    fun b hb => ?_, by rw [acc_eq_edgePairs hR]; simp [edgePairs]⟩
  · have h1 := Nat.mul_sub_one G.colours G.colours
    have h2 : G.colours ≤ G.colours * G.colours := Nat.le_mul_self _
    omega
  · have h1 : (G.colours * G.vertices + G.colours * G.colours * G.vertices) * G.vertices
        ≤ (G.colours * G.vertices + G.colours * G.colours * G.vertices) * G.vertices * c2 G :=
      Nat.le_mul_of_pos_right _ hc2
    have h2 := c3_eq G
    have := hC3 h
    omega
  · have h1 : c2 G * (p - q) ≤ G.vertices * c2 G := by
      rw [Nat.mul_comm (G.vertices)]; exact Nat.mul_le_mul_left _ (by omega)
    have := hC2 h
    have := hC3 h
    omega
  · have h1 : b * (b - 1) ≤ G.colours * (G.colours - 1) :=
      Nat.mul_le_mul hb (by omega)
    omega

theorem header1_spec :
    Spec (bnd x G) (fun σ => H0 x σ ∧ Big x G) header1
      (fun _ σ' => H1 x G σ') 60 := by
  run_vcg
  all_goals have h0 := ‹H0 x σ›
  all_goals have hbig := ‹Big x G›
  all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hout, hrk, hE, heu, hev, htu, htv⟩ := h0
  all_goals have hvn := hbig.vn_eq
  all_goals have hkk := hbig.kk_eq
  all_goals have h1 := hbig.small
  all_goals have h2 := hbig.kn1
  all_goals have h3 := hbig.c2B
  all_goals have h4 := hbig.kk1
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · repeat' (first | exact ‹H0 x σ› | refine H0.setVar ?_ _ _ (by decide))
    all_goals simp [hn, hk, hvn, hkk, c1, c2, Nat.choose_two_right]
  all_goals try simp [hn, hm, hk, hvn, hkk]
  all_goals omega

def H2 (x : List ℕ) (G : Instance) (σ : Env) : Prop :=
  H1 x G σ ∧ σ.vars "M" = nMach G ∧ σ.vars "nc" = nCJob G ∧
    σ.vars "nkc" = nVJob G + nCJob G ∧ σ.vars "nJ" = nJobs G ∧ σ.vars "N" = nJobs G + 1

theorem header2_spec :
    Spec (bnd x G) (fun σ => H1 x G σ ∧ Big x G) header2
      (fun _ σ' => H2 x G σ') 60 := by
  run_vcg
  all_goals have h1' := ‹H1 x G σ›
  all_goals have hbig := ‹Big x G›
  all_goals obtain ⟨⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hout, hrk, hE, heu, hev, htu, htv⟩,
    hK, hc1, hc2, hval⟩ := h1'
  all_goals have hvn := hbig.vn_eq
  all_goals have hkk := hbig.kk_eq
  all_goals have hb1 := hbig.small
  all_goals have hb2 := hbig.kkB
  all_goals have hb3 := hbig.ncB
  all_goals have hb4 := hbig.kk1
  all_goals have hb5 := hbig.accLen
  all_goals have hnJ : nJobs G = G.vertices * G.colours + G.colours * G.colours * G.vertices
      + nEJob G := rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · repeat' (first | exact ‹H1 x G σ› | refine H1.setVar ?_ _ _ (by decide))
    all_goals simp [hn, hk, hvn, hkk, hval, hnk, hE, hb5, nMach, nJobs]
  all_goals try simp [hn, hm, hk, hvn, hkk, hval, hnk, hE, hb5]
  all_goals try omega
  all_goals (rw [Nat.choose_two_right]; omega)

theorem ctx_of_H2 {σ : Env} (h : H2 x G σ) (hW : σ.vars "W" = targetWeight G)
    (hc3 : 1 < G.colours → σ.vars "c3" = c3 G) : Ctx x G σ ∧ σ.out = [] := by
  obtain ⟨⟨⟨hB, hout, hrk, hE⟩, hK, hc1, hc2, hval⟩, hM, hnc, hnkc, hnJ, hN⟩ := h
  exact ⟨⟨hB, hrk, hE, hK, hc1, hc2, hval, hM, hnc, hnkc, hnJ, hN, hW, hc3⟩, hout⟩

theorem header3_spec :
    Spec (bnd x G) (fun σ => H2 x G σ ∧ Big x G) header3
      (fun _ σ' => Ctx x G σ' ∧ σ'.out = []) 80 := by
  run_vcg
  all_goals have h2' := ‹H2 x G σ›
  all_goals have hbig := ‹Big x G›
  all_goals obtain ⟨⟨⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hout, hrk, hE, heu, hev, htu, htv⟩,
    hK, hc1, hc2, hval⟩, hM, hnc, hnkc, hnJ, hN⟩ := h2'
  all_goals have hvn := hbig.vn_eq
  all_goals have hkk := hbig.kk_eq
  all_goals have hb1 := hbig.small
  all_goals have hb2 := hbig.w0
  all_goals have hb3 := hbig.kn1
  all_goals have hb4 := hbig.ncB
  all_goals have hb5 := hbig.knB
  all_goals first
    | (have hk1 : 1 < G.colours := by
        simpa [hk, hkk] using ‹1 < (Env.setVar σ "W" _).vars "k"›)
    | skip
  · refine ctx_of_H2 ?_ ?_ ?_
    · repeat' (first | exact ‹H2 x G σ› | refine H2.setVar ?_ _ _ (by decide))
    · simp [hn, hk, hvn, hkk, hc1, hc2, hval, hnc, c3_eq, targetWeight]
      omega
    · intro _
      simp [hn, hk, hvn, hkk, hc1, hc2, hval, hnc, c3_eq]
  · have hk0 : ¬ 1 < G.colours := by
      simpa [hk, hkk] using ‹¬ 1 < (Env.setVar σ "W" _).vars "k"›
    refine ctx_of_H2 ?_ ?_ ?_
    · repeat' (first | exact ‹H2 x G σ› | refine H2.setVar ?_ _ _ (by decide))
    · have hch : G.colours.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hn, hk, hvn, hkk, hc1, targetWeight, hch]
    · intro h; exact absurd h hk0
  all_goals try simp [hn, hk, hvn, hkk, hc1, hc2, hval, hnc, c3_eq]
  all_goals try omega
  all_goals have hb6 := hbig.c2B
  all_goals have hncE : nCJob G = G.colours * G.colours * G.vertices := rfl
  all_goals try omega
  all_goals try (simp only [c1, c2]; omega)
  all_goals try simp only [nCJob]
  all_goals have hb7 := hbig.kk1
  all_goals have hb8 := two_choose G.colours
  all_goals try omega
  all_goals first
    | (have := hbig.m1 hk1; have := hbig.m3 hk1; have := hbig.m4 hk1; have := hbig.c3B hk1
       have := c3_eq G
       omega)
    | skip

end Lax470956Proofs.Construction1Ctx
