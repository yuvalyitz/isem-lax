import Lax470956Proofs.Construction1Info

/-!
Construction 1 as a word RAM program: the five passes that write the blocks.
-/

namespace Lax470956Proofs.Construction1Passes

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.MulticolouredClique Lax470956.Construction1
open Lax470956Proofs.Construction1Shape Lax470956Proofs.Construction1Prog
open Lax470956Proofs.Construction1Read Lax470956Proofs.Construction1Ctx
open Lax470956Proofs.Construction1Info

variable {x : List ℕ} {G : Instance}

/-- A pass in progress: the counter has written the first `j` entries of its block. -/
def BInv (x : List ℕ) (G : Instance) (N : ℕ) (out0 : List ℕ) (g : ℕ → ℕ) (σ : Env) : Prop :=
  Ctx x G σ ∧ σ.vars "j" ≤ N ∧ σ.out = out0 ++ (List.range (σ.vars "j")).map g

lemma map_range_succ (g : ℕ → ℕ) (j : ℕ) :
    (List.range (j + 1)).map g = (List.range j).map g ++ [g j] := by
  rw [List.range_succ, List.map_append]; rfl

lemma procOf_lt (hR : Reads x G) {j : ℕ} (hj : j < nJobs G) : procOf G j < bnd x G := by
  obtain ⟨h1, h2⟩ := raw_lt hR hj
  have := (big hR).small
  simp only [procOf]; omega

lemma dueOf_lt (hR : Reads x G) {j : ℕ} (hj : j < nJobs G) : dueOf G j < bnd x G := by
  obtain ⟨h1, h2⟩ := raw_lt hR hj
  have := (big hR).small
  simp only [dueOf]; omega

lemma wtOf_lt (hR : Reads x G) {j : ℕ} (hj : j < nJobs G) : wtOf G j < bnd x G := by
  have hbig := big hR
  have hsm := hbig.small
  have hc2B := hbig.c2B
  by_cases h1 : j < nVJob G
  · simp only [wtOf, h1, if_true]
    split_ifs
    · omega
    · simp only [c1]; omega
  · by_cases h2 : j < nVJob G + nCJob G
    · simp only [wtOf, h1, h2, if_true, if_false]
      by_cases hok : CJobOk G (j - nVJob G)
      · have hz := hok.2.2.1
        have hk1 : 1 < G.colours := by have := hok.1; have := hok.2.1; omega
        have ha := hbig.c2p hk1 _ 0 (pos_le hR hz)
        have hb := hbig.c2p hk1 G.vertices (@pos G (cjZ G (j - nVJob G))) (le_refl _)
        simp only [Nat.sub_zero] at ha
        simp only [hok, if_true]
        split_ifs <;> omega
      · simp only [hok, if_false]; omega
    · have hq : j - nVJob G - nCJob G < nEJob G := by simp only [nJobs] at hj; omega
      have hok : EJobOk G (j - nVJob G - nCJob G) := hq
      obtain ⟨hclt, hcVl⟩ := Lax470956Proofs.Construction1Emit.edge_col_lt (G := G) hq
      have hk1 : 1 < G.colours := by omega
      have hVlt : ejV G (j - nVJob G - nCJob G) < G.vertices := by
        rw [ejV, List.getElem?_eq_getElem hq]; simp
      have hc := hbig.c2p hk1 _ (@pos G (ejU G (j - nVJob G - nCJob G))) (pos_le hR hVlt)
      simp only [wtOf, h1, h2, if_false, hok, if_true]
      exact hc

theorem procBody_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G)
      (fun σ => BInv x G (nJobs G) out0 (procOf G) σ ∧ σ.vars "j" < nJobs G) procBody
      (fun σ σ' => BInv x G (nJobs G) out0 (procOf G) σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 320 := by
  have hsm := (big hR).small
  run_vcg [info_spec hR]
  all_goals obtain ⟨hctx, hjle, hout⟩ := ‹BInv x G (nJobs G) out0 (procOf G) σ›
  all_goals have hjlt := ‹σ.vars "j" < nJobs G›
  all_goals try exact ⟨hctx, hjlt⟩
  all_goals obtain ⟨hctx', ⟨hj', hout', ho'⟩, hP, hD, hWt, hel, hel2⟩ :=
    ‹Ctx x G _ ∧ Fr σ _ ∧ Done G (σ.vars "j") _›
  all_goals have hb := procOf_lt hR hjlt
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · repeat' (first | exact hctx' | refine Ctx.setVar ?_ _ _ (by decide))
    · simp [hj']; omega
    · simp [hj', hout', hout, map_range_succ, hP]
    · simp [hj']
  all_goals try simp [hj', hP]
  all_goals try omega

theorem dueBody_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G)
      (fun σ => BInv x G (nJobs G) out0 (dueOf G) σ ∧ σ.vars "j" < nJobs G) dueBody
      (fun σ σ' => BInv x G (nJobs G) out0 (dueOf G) σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 320 := by
  have hsm := (big hR).small
  run_vcg [info_spec hR]
  all_goals obtain ⟨hctx, hjle, hout⟩ := ‹BInv x G (nJobs G) out0 (dueOf G) σ›
  all_goals have hjlt := ‹σ.vars "j" < nJobs G›
  all_goals try exact ⟨hctx, hjlt⟩
  all_goals obtain ⟨hctx', ⟨hj', hout', ho'⟩, hP, hD, hWt, hel, hel2⟩ :=
    ‹Ctx x G _ ∧ Fr σ _ ∧ Done G (σ.vars "j") _›
  all_goals have hb := dueOf_lt hR hjlt
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · repeat' (first | exact hctx' | refine Ctx.setVar ?_ _ _ (by decide))
    · simp [hj']; omega
    · simp [hj', hout', hout, map_range_succ, hD]
    · simp [hj']
  all_goals try simp [hj', hD]
  all_goals try omega

theorem wtBody_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G)
      (fun σ => BInv x G (nJobs G) out0 (wtOf G) σ ∧ σ.vars "j" < nJobs G) wtBody
      (fun σ σ' => BInv x G (nJobs G) out0 (wtOf G) σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 320 := by
  have hsm := (big hR).small
  run_vcg [info_spec hR]
  all_goals obtain ⟨hctx, hjle, hout⟩ := ‹BInv x G (nJobs G) out0 (wtOf G) σ›
  all_goals have hjlt := ‹σ.vars "j" < nJobs G›
  all_goals try exact ⟨hctx, hjlt⟩
  all_goals obtain ⟨hctx', ⟨hj', hout', ho'⟩, hP, hD, hWt, hel, hel2⟩ :=
    ‹Ctx x G _ ∧ Fr σ _ ∧ Done G (σ.vars "j") _›
  all_goals have hb := wtOf_lt hR hjlt
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · repeat' (first | exact hctx' | refine Ctx.setVar ?_ _ _ (by decide))
    · simp [hj']; omega
    · simp [hj', hout', hout, map_range_succ, hWt]
    · simp [hj']
  all_goals try simp [hj', hWt]
  all_goals try omega

/-! ### The Three Scalar Passes, as Loops -/

lemma nJ_of_ctx {σ : Env} (h : Ctx x G σ) : σ.vars "nJ" = nJobs G :=
  h.2.2.2.2.2.2.2.2.2.2.1

lemma N_of_ctx {σ : Env} (h : Ctx x G σ) : σ.vars "N" = nJobs G + 1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

lemma nJ_lt_bnd (hR : Reads x G) : nJobs G + 1 < bnd x G := by
  have := (big hR).small; omega

theorem procLoop_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G) (fun σ => BInv x G (nJobs G) out0 (procOf G) (σ.setVar "j" 0))
      (jobLoop procBody "nJ")
      (fun _ σ' => BInv x G (nJobs G) out0 (procOf G) σ' ∧ σ'.vars "j" = nJobs G)
      (324 * nJobs G + 6) :=
  Spec.forRangeZero "j" "nJ" (BInv x G (nJobs G) out0 (procOf G)) (nJobs G) 320
    (by have := nJ_lt_bnd hR; omega) (fun _ h => h.2.1) (fun _ h => nJ_of_ctx h.1)
    (procBody_spec hR out0)

theorem dueLoop_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G) (fun σ => BInv x G (nJobs G) out0 (dueOf G) (σ.setVar "j" 0))
      (jobLoop dueBody "nJ")
      (fun _ σ' => BInv x G (nJobs G) out0 (dueOf G) σ' ∧ σ'.vars "j" = nJobs G)
      (324 * nJobs G + 6) :=
  Spec.forRangeZero "j" "nJ" (BInv x G (nJobs G) out0 (dueOf G)) (nJobs G) 320
    (by have := nJ_lt_bnd hR; omega) (fun _ h => h.2.1) (fun _ h => nJ_of_ctx h.1)
    (dueBody_spec hR out0)

theorem wtLoop_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G) (fun σ => BInv x G (nJobs G) out0 (wtOf G) (σ.setVar "j" 0))
      (jobLoop wtBody "nJ")
      (fun _ σ' => BInv x G (nJobs G) out0 (wtOf G) σ' ∧ σ'.vars "j" = nJobs G)
      (324 * nJobs G + 6) :=
  Spec.forRangeZero "j" "nJ" (BInv x G (nJobs G) out0 (wtOf G)) (nJobs G) 320
    (by have := nJ_lt_bnd hR; omega) (fun _ h => h.2.1) (fun _ h => nJ_of_ctx h.1)
    (wtBody_spec hR out0)

/-! ### The Offset Pass -/

lemma elig_len_le (G : Instance) (j : ℕ) : (eligOf G j).length ≤ 2 := by
  classical
  simp only [eligOf]
  split_ifs <;> simp

lemma offOf_succ (G : Instance) (j : ℕ) :
    offOf G (j + 1) = offOf G j + (eligOf G j).length := by
  simp [offOf, List.range_succ]

lemma offOf_le (G : Instance) (j : ℕ) : offOf G j ≤ 2 * j := by
  induction j with
  | zero => simp [offOf]
  | succ p ih => rw [offOf_succ]; have := elig_len_le G p; omega

lemma Ctx.of_write {σ : Env} (h : Ctx x G σ) (l : List ℕ) :
    Ctx x G { vars := σ.vars, arrs := σ.arrs, inp := σ.inp, out := l } := by
  simpa [Ctx, Construction1Tables.Base, Construction1Tables.Ranked, EDone] using h

lemma el_eq {G : Instance} {j a b e : ℕ} (h : eligOf G j = [a, b].take e) (he : e ≤ 2) :
    (eligOf G j).length = e := by
  rw [h, List.length_take]; simp; omega

/-- The offset pass in progress: `o` is the running sum of the eligibility lengths. -/
def OInv (x : List ℕ) (G : Instance) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x G σ ∧ σ.vars "j" ≤ nJobs G + 1 ∧ (σ.vars "j" ≤ nJobs G → σ.vars "o" = offOf G (σ.vars "j")) ∧
    σ.out = out0 ++ (List.range (σ.vars "j")).map (offOf G)

theorem offBody_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G) (fun σ => OInv x G out0 σ ∧ σ.vars "j" < nJobs G + 1) offBody
      (fun σ σ' => OInv x G out0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 330 := by
  have hsm := (big hR).small
  run_vcg [info_spec hR]
  all_goals obtain ⟨hctx, hjle, ho, hout⟩ := ‹OInv x G out0 σ›
  all_goals have hjlt := ‹σ.vars "j" < nJobs G + 1›
  all_goals have hnJ := nJ_of_ctx hctx
  all_goals have hov := ho (by omega)
  all_goals have hol := offOf_le G (σ.vars "j")
  · rename_i hc w hw
    obtain ⟨hctx', ⟨hj', hout', ho'⟩, hP, hD, hWt, hel, hel2⟩ := hw
    simp only at hj' hout' ho' hel hc
    have hlen := el_eq hel hel2
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · repeat' (first | exact hctx' | refine Ctx.setVar ?_ _ _ (by decide))
    · simp [hj']; omega
    · intro _
      simp [hj', ho', hov, offOf_succ, hlen]
    · simp [hj', hout', hout, map_range_succ, hov]
    · simp [hj']
  · rename_i hc
    simp only [hnJ] at hc
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (Ctx.of_write hctx _).setVar _ _ (by decide)
    · simp; omega
    · intro h; simp at h; omega
    · simp [hout, map_range_succ, hov]
    · simp
  all_goals try simp [hnJ]
  all_goals try omega
  all_goals try
    (refine ⟨Ctx.of_write hctx _, ?_⟩
     have hc : σ.vars "j" < σ.vars "nJ" := by assumption
     omega)
  all_goals
    (obtain ⟨hctx', ⟨hj', hout', ho'⟩, hP, hD, hWt, hel, hel2⟩ :=
      ‹Ctx x G _ ∧ Fr _ _ ∧ Done G _ _›
     simp only at hj' ho'
     omega)

theorem offLoop_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G) (fun σ => OInv x G out0 (σ.setVar "j" 0)) (jobLoop offBody "N")
      (fun _ σ' => OInv x G out0 σ' ∧ σ'.vars "j" = nJobs G + 1)
      (334 * (nJobs G + 1) + 6) :=
  Spec.forRangeZero "j" "N" (OInv x G out0) (nJobs G + 1) 330
    (by have := (big hR).small; omega) (fun _ h => h.2.1) (fun _ h => N_of_ctx h.1)
    (offBody_spec hR out0)

/-! ### The Target Pass -/

lemma flatMap_range_succ (g : ℕ → List ℕ) (j : ℕ) :
    (List.range (j + 1)).flatMap g = (List.range j).flatMap g ++ g j := by
  rw [List.range_succ, List.flatMap_append]; simp

lemma nMach_lt_bnd (hR : Reads x G) : nMach G < bnd x G := by
  have h1 := (big hR).kk1
  have h2 := two_choose G.colours
  have h3 := (big hR).small
  simp only [nMach]; omega

lemma mem_take_first {a b e : ℕ} (h : 0 < e) : a ∈ [a, b].take e := by
  rcases e with _ | e
  · omega
  · simp

lemma mem_take_second {a b e : ℕ} (h : 1 < e) : b ∈ [a, b].take e := by
  rcases e with _ | _ | e
  · omega
  · omega
  · simp

/-- The target pass in progress. -/
def TInv (x : List ℕ) (G : Instance) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x G σ ∧ σ.vars "j" ≤ nJobs G ∧
    σ.out = out0 ++ (List.range (σ.vars "j")).flatMap (eligOf G)

theorem tgtBody_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G) (fun σ => TInv x G out0 σ ∧ σ.vars "j" < nJobs G) tgtBody
      (fun σ σ' => TInv x G out0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 330 := by
  have hsm := (big hR).small
  have hM := nMach_lt_bnd hR
  run_vcg [info_spec hR]
  all_goals obtain ⟨hctx, hjle, hout⟩ := ‹TInv x G out0 σ›
  all_goals have hjlt := ‹σ.vars "j" < nJobs G›
  all_goals try exact ⟨hctx, hjlt⟩
  all_goals obtain ⟨hctx', ⟨hj', hout', ho'⟩, hP, hD, hWt, hel, hel2⟩ :=
    ‹Ctx x G _ ∧ Fr σ _ ∧ Done G (σ.vars "j") _›
  all_goals have hmem := fun v hv => Lax470956Proofs.Construction1Emit.elig_lt (G := G) hjlt (v := v) hv
  · rename_i hc1 hc2
    simp only at hc2
    have hE : _ = 2 := Nat.le_antisymm hel2 hc2
    rw [hE] at hel
    refine ⟨⟨(Ctx.of_write (Ctx.of_write hctx' _) _).setVar _ _ (by decide), ?_, ?_⟩, ?_⟩
    · simp [hj']; omega
    · simp [hj', hout', hout, flatMap_range_succ, hel]
    · simp [hj']
  · rename_i hc1 hc2
    simp only at hc2
    have hE : _ = 1 := Nat.le_antisymm (Nat.le_of_not_lt hc2) hc1
    rw [hE] at hel
    refine ⟨⟨(Ctx.of_write hctx' _).setVar _ _ (by decide), ?_, ?_⟩, ?_⟩
    · simp [hj']; omega
    · simp [hj', hout', hout, flatMap_range_succ, hel]
    · simp [hj']
  · rename_i hc1 hc2
    omega
  · rename_i hc1 hc2
    have hE : _ = 0 := Nat.eq_zero_of_not_pos hc1
    rw [hE] at hel
    refine ⟨⟨hctx'.setVar _ _ (by decide), ?_, ?_⟩, ?_⟩
    · simp [hj']; omega
    · simp [hj', hout', hout, flatMap_range_succ, hel]
    · simp [hj']
  all_goals try simp [hj']
  all_goals try omega
  · have := hmem _ (by rw [hel]; exact mem_take_first ‹0 < _›)
    omega
  · rename_i hc1 _ hc2
    simp only at hc2
    have := hmem _ (by rw [hel]; exact mem_take_second hc2)
    omega

theorem tgtLoop_spec (hR : Reads x G) (out0 : List ℕ) :
    Spec (bnd x G) (fun σ => TInv x G out0 (σ.setVar "j" 0)) (jobLoop tgtBody "nJ")
      (fun _ σ' => TInv x G out0 σ' ∧ σ'.vars "j" = nJobs G) (334 * nJobs G + 6) :=
  Spec.forRangeZero "j" "nJ" (TInv x G out0) (nJobs G) 330
    (by have := nJ_lt_bnd hR; omega) (fun _ h => h.2.1) (fun _ h => nJ_of_ctx h.1)
    (tgtBody_spec hR out0)

end Lax470956Proofs.Construction1Passes
