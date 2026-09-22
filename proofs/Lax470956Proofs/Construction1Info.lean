import Lax470956Proofs.Construction1Setup
import Lax470956Proofs.Construction1Emit

/-!
Construction 1 as a word RAM program: everything about job `j`.
-/

namespace Lax470956Proofs.Construction1Info

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.MulticolouredClique Lax470956.Construction1
open Lax470956Proofs.Construction1Shape Lax470956Proofs.Construction1Prog
open Lax470956Proofs.Construction1Read Lax470956Proofs.Construction1Rank
open Lax470956Proofs.Construction1Edges Lax470956Proofs.Construction1Tables
open Lax470956Proofs.Construction1Ctx

variable {x : List ℕ} {G : Instance}

/-! ### The tables, read as the construction's own accessors -/

lemma colr_eq_col (hR : Reads x G) {v : ℕ} (hv : v < G.vertices) :
    colr x v = col (G := G) v := by
  rw [hR.colr_eq ⟨v, hv⟩, col, dif_pos hv]

lemma col_lt {v : ℕ} (hv : v < G.vertices) : col (G := G) v < G.colours := by
  rw [col, dif_pos hv]; exact (G.colour ⟨v, hv⟩).isLt

lemma pos_eq (hR : Reads x G) {v : ℕ} (hv : v < G.vertices) :
    pos (G := G) v = before (colr x) (vn x) v + 1 := by
  rw [pos, dif_pos hv, rank_eq, hR.vn_eq]
  congr 1
  exact before_congr hv fun u hu => (colr_eq_col hR hu).symm

lemma before_lt {cf : ℕ → ℕ} {n v : ℕ} (hv : v < n) : before cf n v < n := by
  have h1 : before cf n v
      ≤ ((List.range n).filter fun u => decide (u ≠ v)).length := by
    simp only [before]
    refine List.Sublist.length_le (List.monotone_filter_right _ fun u hu => ?_)
    simp only [decide_eq_true_eq] at hu ⊢
    rintro rfl
    omega
  have h2 := List.length_eq_length_filter_add (l := List.range n) fun u => decide (u ≠ v)
  have h3 : 0 < ((List.range n).filter fun u => !decide (u ≠ v)).length :=
    List.length_pos_of_mem (a := v) (by simp [hv])
  simp only [List.length_range] at h2
  omega

lemma pos_le (hR : Reads x G) {v : ℕ} (hv : v < G.vertices) : pos (G := G) v ≤ G.vertices := by
  rw [pos_eq hR hv]
  have := before_lt (cf := colr x) (n := vn x) (v := v) (by rw [hR.vn_eq]; exact hv)
  have hvn := hR.vn_eq
  omega

lemma rank_read (hR : Reads x G) {σ : Env} (h : Ranked x σ) {v : ℕ} (hv : v < G.vertices) :
    (σ.arrs "r").getD v 0 = pos (G := G) v := by
  rw [pos_eq hR hv]; exact h.2 v (by rw [hR.vn_eq]; exact hv)

/-- The edge table holds the construction's enumeration. -/
lemma edge_read (hR : Reads x G) {σ : Env} (h : EDone x σ) {q : ℕ} (hq : q < nEJob G) :
    (σ.arrs "eu").getD q 0 = ejU G q ∧ (σ.arrs "ev").getD q 0 = ejV G q ∧
      ejU G q < G.vertices ∧ ejV G q < G.vertices ∧ σ.vars "E" = nEJob G := by
  obtain ⟨hE, heu, hev, htu, htv⟩ := h
  have hacc := acc_eq_edgePairs hR
  have hlen : (acc x (2 * ve x)).length = nEJob G := by rw [hacc]; simp [edgePairs]
  rw [hacc] at htu htv
  rw [hlen] at hE
  have hqu : q < (σ.arrs "eu").length := by
    have : ((σ.arrs "eu").take (σ.vars "E")).length = nEJob G := by rw [htu]; simp [edgePairs]
    simp only [List.length_take] at this; omega
  have hqv : q < (σ.arrs "ev").length := by
    have : ((σ.arrs "ev").take (σ.vars "E")).length = nEJob G := by rw [htv]; simp [edgePairs]
    simp only [List.length_take] at this; omega
  have h1 : (σ.arrs "eu").getD q 0 = ejU G q := by
    have := congrArg (fun l => l.getD q 0) htu
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hE, hq, if_true] at this
    rw [List.getD_eq_getElem?_getD, this, ejU, edgePairs]
    simp [List.getElem?_map]
    rcases (edgeList G)[q]? with _ | p <;> rfl
  have h2 : (σ.arrs "ev").getD q 0 = ejV G q := by
    have := congrArg (fun l => l.getD q 0) htv
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hE, hq, if_true] at this
    rw [List.getD_eq_getElem?_getD, this, ejV, edgePairs]
    simp [List.getElem?_map]
    rcases (edgeList G)[q]? with _ | p <;> rfl
  refine ⟨h1, h2, ?_, ?_, hE⟩
  · rw [ejU, List.getElem?_eq_getElem hq]; simp
  · rw [ejV, List.getElem?_eq_getElem hq]; simp

/-! ### Vertex jobs -/

/-- What a pass keeps while it looks a job up. -/
def Fr (σ σ' : Env) : Prop :=
  σ'.vars "j" = σ.vars "j" ∧ σ'.out = σ.out ∧ σ'.vars "o" = σ.vars "o"

theorem vDecode_spec (hR : Reads x G) :
    Spec (bnd x G) (fun σ => Ctx x G σ ∧ σ.vars "j" < nVJob G) vDecode
      (fun σ σ' => Ctx x G σ' ∧ Fr σ σ' ∧ σ'.vars "z" = vjVert G (σ.vars "j") ∧
        σ'.vars "cc" = vjCol G (σ.vars "j") ∧
        σ'.vars "cz" = col (G := G) (vjVert G (σ.vars "j")) ∧
        σ'.vars "pz" = pos (G := G) (vjVert G (σ.vars "j")) ∧
        σ'.vars "E1" = validation G) 40 := by
  refine Spec.pre (P := fun σ => Ctx x G σ ∧ σ.vars "j" < nVJob G ∧
      0 < G.colours ∧ σ.vars "j" / G.colours < G.vertices ∧
      σ.vars "j" - σ.vars "j" / G.colours * G.colours = σ.vars "j" % G.colours ∧
      σ.vars "j" / G.colours * G.colours ≤ σ.vars "j" ∧
      σ.vars "j" % G.colours < G.colours ∧
      ReadsB x G ∧ Big x G) ?_ ?_
  · run_vcg
    all_goals have hctx := ‹Ctx x G σ›
    all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hrk, hed, hK, hc1, hc2, hval, hM, hnc,
      hnkc, hnJ, hN, hW, hc3⟩ := hctx
    all_goals obtain ⟨hoffB, htgtB, hcolB, hlenB, hblen⟩ := ‹ReadsB x G›
    all_goals have hbig := ‹Big x G›
    all_goals have hvn := hbig.vn_eq
    all_goals have hkk := hbig.kk_eq
    all_goals have hsm := hbig.small
    all_goals have hz := ‹σ.vars "j" / G.colours < G.vertices›
    all_goals have hsub := ‹σ.vars "j" - σ.vars "j" / G.colours * G.colours = _›
    all_goals have hjlt := ‹σ.vars "j" < nVJob G›
    all_goals have hnJe : nJobs G = nVJob G + nCJob G + nEJob G := rfl
    all_goals have hrz : (σ.arrs "r")[σ.vars "j" / G.colours]?.getD 0
        = @pos G (σ.vars "j" / G.colours) :=
      (by rw [← List.getD_eq_getElem?_getD]; exact rank_read hR hrk hz)
    all_goals have hpz := pos_le hR hz
    all_goals have hcz := colr_eq_col hR hz
    all_goals have hrlen : (σ.arrs "r").length = G.vertices := by rw [hrk.1, hvn]
    all_goals have hoc : ∀ v, off x (G.vertices + 1 + 2 * ve x + v) = colr x v :=
      fun v => (by rw [← hvn]; exact off_col x v)
    all_goals have hch1 := hbig.kk1
    all_goals have hch2 := two_choose G.colours
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · repeat' (first | exact ‹Ctx x G σ› | refine Ctx.setVar ?_ _ _ (by decide))
      all_goals simp [Fr, hn, hm, ha, htb, hcb, hk, hnk, hvn, hkk, hsub, hval, body_off',
        hrz, hoc, hcz, vjVert, vjCol]
    all_goals try simp [hn, hm, ha, htb, hcb, hk, hnk, hvn, hkk, hsub, hval, body_off',
      hrz, hoc, hcz, hrlen]
    all_goals try omega
    all_goals try (rw [← hcz]; apply hcolB; omega)
  · rintro σ ⟨hctx, hj⟩
    have hpos : 0 < G.colours := by
      rcases Nat.eq_zero_or_pos G.colours with h | h
      · simp [nVJob, h] at hj
      · exact h
    refine ⟨hctx, hj, hpos, (Nat.div_lt_iff_lt_mul hpos).mpr hj, sub_div_mul _ _,
      Nat.div_mul_le_self _ _, Nat.mod_lt _ hpos, readsB hR, big hR⟩

/-- The raw numbers of job `j` are in the scalars. -/
def Raw (G : Instance) (j : ℕ) (σ' : Env) : Prop :=
  σ'.vars "rp" = rawProc G j ∧ σ'.vars "rd" = rawDue G j ∧ σ'.vars "Wt" = wtOf G j ∧
    eligOf G j = [σ'.vars "E1", σ'.vars "E2"].take (σ'.vars "EL") ∧ σ'.vars "EL" ≤ 2

/-- The state between a vertex job's decoding and its numbers. -/
def VDec (x : List ℕ) (G : Instance) (σ : Env) : Prop :=
  Ctx x G σ ∧ σ.vars "j" < nVJob G ∧ σ.vars "z" = vjVert G (σ.vars "j") ∧
    σ.vars "cc" = vjCol G (σ.vars "j") ∧
    σ.vars "cz" = col (G := G) (vjVert G (σ.vars "j")) ∧
    σ.vars "pz" = pos (G := G) (vjVert G (σ.vars "j")) ∧ σ.vars "E1" = validation G

theorem vBody_spec (hR : Reads x G) :
    Spec (bnd x G) (VDec x G) (.ite (.eq (V "cc") (V "cz")) vOwn vOther)
      (fun σ σ' => Ctx x G σ' ∧ Fr σ σ' ∧ Raw G (σ.vars "j") σ') 60 := by
  refine Spec.pre (P := fun σ => VDec x G σ ∧ Big x G ∧
      vjVert G (σ.vars "j") < G.vertices ∧ vjCol G (σ.vars "j") < G.colours) ?_ ?_
  · run_vcg
    all_goals have hctx0 : Ctx x G σ := (‹VDec x G σ›).1
    all_goals obtain ⟨hctx, hjlt, hz, hcc, hcz, hpz, hE1⟩ := ‹VDec x G σ›
    all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hrk, hed, hK, hc1, hc2, hval, hM, hnc,
      hnkc, hnJ, hN, hW, hc3⟩ := hctx
    all_goals have hbig := ‹Big x G›
    all_goals have hzlt := ‹vjVert G (σ.vars "j") < G.vertices›
    all_goals have hcclt := ‹vjCol G (σ.vars "j") < G.colours›
    all_goals have hczlt := col_lt (G := G) hzlt
    all_goals have hple := pos_le hR hzlt
    all_goals have hKp := hbig.Kp _ hple
    all_goals have hsm := hbig.small
    all_goals have hpe1 := hbig.pe _ (Nat.le_of_lt hcclt)
    all_goals have hpe2 := hbig.pe _ (Nat.le_of_lt hczlt)
    all_goals have hch1 := hbig.kk1
    all_goals have hch2 := two_choose G.colours
    · rename_i hc
      have hown : vjCol G (σ.vars "j") = col (G := G) (vjVert G (σ.vars "j")) := by
        simpa [hcc, hcz] using hc
      refine ⟨?_, ?_, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      · simp [Fr]
      · simp [Raw, rawProc, rawDue, wtOf, eligOf, hjlt, hown, hK, hpz, hE1]
    · rename_i hc1' hc
      have hown : ¬ vjCol G (σ.vars "j") = col (G := G) (vjVert G (σ.vars "j")) := by
        simpa [hcc, hcz] using hc1'
      have hlt : vjCol G (σ.vars "j") < col (G := G) (vjVert G (σ.vars "j")) := by
        simpa [hcc, hcz] using hc
      refine ⟨?_, ?_, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      · simp [Fr]
      · simp [Raw, rawProc, rawDue, wtOf, eligOf, hjlt, hown, hK, hpz, hE1, hcc, hcz, hc1,
          pairIdx, Nat.choose_two_right, Nat.min_eq_left (Nat.le_of_lt hlt),
          Nat.max_eq_right (Nat.le_of_lt hlt)]
    · rename_i hc1' hc
      have hown : ¬ vjCol G (σ.vars "j") = col (G := G) (vjVert G (σ.vars "j")) := by
        simpa [hcc, hcz] using hc1'
      have hge : col (G := G) (vjVert G (σ.vars "j")) ≤ vjCol G (σ.vars "j") := by
        simpa [hcc, hcz] using hc
      refine ⟨?_, ?_, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      · simp [Fr]
      · simp [Raw, rawProc, rawDue, wtOf, eligOf, hjlt, hown, hK, hpz, hE1, hcc, hcz, hc1,
          pairIdx, Nat.choose_two_right, Nat.min_eq_right hge, Nat.max_eq_left hge]
    all_goals try simp [hK, hpz, hcc, hcz, hc1, hE1]
    all_goals try omega
    all_goals try (simp only [c1]; omega)
  · rintro σ hv
    have hv' := hv
    obtain ⟨hctx, hj, -⟩ := hv
    have hpos : 0 < G.colours := by
      rcases Nat.eq_zero_or_pos G.colours with h | h
      · simp [nVJob, h] at hj
      · exact h
    exact ⟨hv', big hR, (Nat.div_lt_iff_lt_mul hpos).mpr hj, Nat.mod_lt _ hpos⟩

/-! ### Colour combination slots -/

/-- The state between a combination slot's decoding and its numbers. -/
def CDec (x : List ℕ) (G : Instance) (σ : Env) : Prop :=
  Ctx x G σ ∧ nVJob G ≤ σ.vars "j" ∧ σ.vars "j" < nVJob G + nCJob G ∧
    σ.vars "A" = cjA G (σ.vars "j" - nVJob G) ∧ σ.vars "Bc" = cjB G (σ.vars "j" - nVJob G) ∧
    σ.vars "z" = cjZ G (σ.vars "j" - nVJob G) ∧
    σ.vars "cz" = col (G := G) (cjZ G (σ.vars "j" - nVJob G)) ∧
    σ.vars "pz" = pos (G := G) (cjZ G (σ.vars "j" - nVJob G))

theorem cDecode_spec (hR : Reads x G) :
    Spec (bnd x G)
      (fun σ => Ctx x G σ ∧ nVJob G ≤ σ.vars "j" ∧ σ.vars "j" < nVJob G + nCJob G) cDecode
      (fun σ σ' => CDec x G σ' ∧ Fr σ σ') 60 := by
  refine Spec.pre (P := fun σ => Ctx x G σ ∧ nVJob G ≤ σ.vars "j" ∧
      σ.vars "j" < nVJob G + nCJob G ∧ 0 < G.vertices ∧ 0 < G.colours ∧
      (σ.vars "j" - nVJob G) % G.vertices < G.vertices ∧
      (σ.vars "j" - nVJob G) - (σ.vars "j" - nVJob G) / G.vertices * G.vertices
        = (σ.vars "j" - nVJob G) % G.vertices ∧
      (σ.vars "j" - nVJob G) / G.vertices * G.vertices ≤ σ.vars "j" - nVJob G ∧
      (σ.vars "j" - nVJob G) / G.vertices
          - (σ.vars "j" - nVJob G) / G.vertices / G.colours * G.colours
        = (σ.vars "j" - nVJob G) / G.vertices % G.colours ∧
      (σ.vars "j" - nVJob G) / G.vertices / G.colours * G.colours
        ≤ (σ.vars "j" - nVJob G) / G.vertices ∧
      (σ.vars "j" - nVJob G) / G.vertices ≤ σ.vars "j" - nVJob G ∧
      ReadsB x G ∧ Big x G) ?_ ?_
  · run_vcg
    all_goals have hctx0 := ‹Ctx x G σ›
    all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hrk, hed, hK, hc1, hc2, hval, hM, hnc,
      hnkc, hnJ, hN, hW, hc3⟩ := ‹Ctx x G σ›
    all_goals obtain ⟨hoffB, htgtB, hcolB, hlenB, hblen⟩ := ‹ReadsB x G›
    all_goals have hbig := ‹Big x G›
    all_goals have hvn := hbig.vn_eq
    all_goals have hkk := hbig.kk_eq
    all_goals have hsm := hbig.small
    all_goals have hz := ‹(σ.vars "j" - nVJob G) % G.vertices < G.vertices›
    all_goals have hs1 := ‹(σ.vars "j" - nVJob G) - _ = (σ.vars "j" - nVJob G) % G.vertices›
    all_goals have hs2 := ‹(σ.vars "j" - nVJob G) / G.vertices - _ = _›
    all_goals have hnke : vn x * kk x = nVJob G := by rw [hvn, hkk]
    all_goals have hnJe : nJobs G = nVJob G + nCJob G + nEJob G := rfl
    all_goals have hrz : (σ.arrs "r")[(σ.vars "j" - nVJob G) % G.vertices]?.getD 0
        = @pos G ((σ.vars "j" - nVJob G) % G.vertices) :=
      (by rw [← List.getD_eq_getElem?_getD]; exact rank_read hR hrk hz)
    all_goals have hpz := pos_le hR hz
    all_goals have hcz := colr_eq_col hR hz
    all_goals have hrlen : (σ.arrs "r").length = G.vertices := by rw [hrk.1, hvn]
    all_goals have hoc : ∀ v, off x (G.vertices + 1 + 2 * ve x + v) = colr x v :=
      fun v => (by rw [← hvn]; exact off_col x v)
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      all_goals simp [Fr, hn, hm, ha, htb, hcb, hk, hnk, hnke, hvn, hkk, hs1, hs2, body_off',
        hrz, hoc, hcz, cjA, cjB, cjZ]
      all_goals try omega
    all_goals try simp [hn, hm, ha, htb, hcb, hk, hnk, hnke, hvn, hkk, hs1, hs2, body_off',
      hrz, hoc, hcz, hrlen]
    all_goals try omega
    all_goals try (rw [← hcz]; apply hcolB; omega)
    all_goals have hnv : nVJob G = G.vertices * G.colours := rfl
    all_goals have hncv : nCJob G = G.colours * G.colours * G.vertices := rfl
    all_goals have hq1 := ‹σ.vars "j" < nVJob G + nCJob G›
    all_goals have hq2 := ‹nVJob G ≤ σ.vars "j"›
    all_goals have hq : σ.vars "j" - nVJob G < nCJob G := (by omega)
    all_goals have hncB := hbig.ncB
    all_goals have hdl := ‹(σ.vars "j" - nVJob G) / G.vertices ≤ σ.vars "j" - nVJob G›
    all_goals have hd1 := ‹(σ.vars "j" - nVJob G) / G.vertices * G.vertices ≤ _›
    all_goals have hd2 := ‹(σ.vars "j" - nVJob G) / G.vertices / G.colours * G.colours ≤ _›
    all_goals have hd3 := Nat.div_le_self ((σ.vars "j" - nVJob G) / G.vertices) G.colours
    all_goals (simp only [hnv, hncv] at *; omega)
  · rintro σ ⟨hctx, hj1, hj2⟩
    have hpn : 0 < G.vertices := by
      rcases Nat.eq_zero_or_pos G.vertices with h | h
      · simp [nCJob, h] at hj2; omega
      · exact h
    have hpk : 0 < G.colours := by
      rcases Nat.eq_zero_or_pos G.colours with h | h
      · simp [nCJob, h] at hj2; omega
      · exact h
    exact ⟨hctx, hj1, hj2, hpn, hpk, Nat.mod_lt _ hpn, sub_div_mul _ _,
      Nat.div_mul_le_self _ _, sub_div_mul _ _, Nat.div_mul_le_self _ _,
      Nat.div_le_self _ _, readsB hR, big hR⟩

theorem cBody_spec (hR : Reads x G) :
    Spec (bnd x G) (CDec x G) cBody
      (fun σ σ' => Ctx x G σ' ∧ Fr σ σ' ∧ Raw G (σ.vars "j") σ') 80 := by
  refine Spec.pre (P := fun σ => CDec x G σ ∧ Big x G ∧
      cjZ G (σ.vars "j" - nVJob G) < G.vertices ∧
      cjB G (σ.vars "j" - nVJob G) < G.colours ∧
      cjA G (σ.vars "j" - nVJob G) < G.colours) ?_ ?_
  · run_vcg
    all_goals have hctx0 : Ctx x G σ := (‹CDec x G σ›).1
    all_goals obtain ⟨hctx, hj1, hj2, hA, hB, hz, hcz, hpz⟩ := ‹CDec x G σ›
    all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hrk, hed, hK, hc1, hc2, hval, hM, hnc,
      hnkc, hnJ, hN, hW, hc3⟩ := hctx
    all_goals have hbig := ‹Big x G›
    all_goals have hvn := hbig.vn_eq
    all_goals have hzlt := ‹cjZ G (σ.vars "j" - nVJob G) < G.vertices›
    all_goals have hBlt := ‹cjB G (σ.vars "j" - nVJob G) < G.colours›
    all_goals have hczlt := col_lt (G := G) hzlt
    all_goals have hple := pos_le hR hzlt
    all_goals have hKp := hbig.Kp _ hple
    all_goals have hKn := hbig.Kp _ (le_refl G.vertices)
    all_goals have hKd := hbig.Kd G.vertices (@pos G (cjZ G (σ.vars "j" - nVJob G))) (le_refl _)
    all_goals have hsm := hbig.small
    all_goals have hpe := hbig.pe _ (Nat.le_of_lt hBlt)
    all_goals have hnj : ¬ σ.vars "j" < nVJob G := (by omega)
    all_goals first
      | (have hAB : cjA G (σ.vars "j" - nVJob G) < cjB G (σ.vars "j" - nVJob G) := by
          simpa [hA, hB] using ‹σ.vars "A" < σ.vars "Bc"›)
      | skip
    · rename_i hc
      have hcA : col (G := G) (cjZ G (σ.vars "j" - nVJob G)) = cjA G (σ.vars "j" - nVJob G) := by
        simpa [hcz, hA] using hc
      have hok : CJobOk G (σ.vars "j" - nVJob G) := ⟨hAB, hBlt, hzlt, Or.inl hcA⟩
      refine ⟨?_, ?_, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      · simp [Fr]
      · simp [Raw, rawProc, rawDue, wtOf, eligOf, hnj, hj2, hok, hcA, hK, hpz, hA, hB, hc2,
          pairIdx, Nat.choose_two_right]
    · rename_i hc1' hc
      have hcA : ¬ col (G := G) (cjZ G (σ.vars "j" - nVJob G))
          = cjA G (σ.vars "j" - nVJob G) := by simpa [hcz, hA] using hc1'
      have hcB : col (G := G) (cjZ G (σ.vars "j" - nVJob G)) = cjB G (σ.vars "j" - nVJob G) := by
        simpa [hcz, hB] using hc
      have hok : CJobOk G (σ.vars "j" - nVJob G) := ⟨hAB, hBlt, hzlt, Or.inr hcB⟩
      refine ⟨?_, ?_, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      · simp [Fr]
      · have hcA' : ¬ cjB G (σ.vars "j" - nVJob G) = cjA G (σ.vars "j" - nVJob G) := by omega
        simp [Raw, rawProc, rawDue, wtOf, eligOf, hnj, hj2, hok, hcB, hcA', hK, hpz, hA, hB,
          hc2, hn, hvn, pairIdx, Nat.choose_two_right]
    · rename_i hc1' hc
      have hcA : ¬ col (G := G) (cjZ G (σ.vars "j" - nVJob G))
          = cjA G (σ.vars "j" - nVJob G) := by simpa [hcz, hA] using hc1'
      have hcB : ¬ col (G := G) (cjZ G (σ.vars "j" - nVJob G))
          = cjB G (σ.vars "j" - nVJob G) := by simpa [hcz, hB] using hc
      have hok : ¬ CJobOk G (σ.vars "j" - nVJob G) := fun h => by
        rcases h.2.2.2 with h' | h'
        · exact hcA h'
        · exact hcB h'
      refine ⟨?_, ?_, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      · simp [Fr]
      · simp [Raw, rawProc, rawDue, wtOf, eligOf, hnj, hj2, hok]
    · rename_i hc
      have hok : ¬ CJobOk G (σ.vars "j" - nVJob G) := fun h => by
        have := h.1
        rw [← hA, ← hB] at this
        exact hc this
      refine ⟨?_, ?_, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      · simp [Fr]
      · simp [Raw, rawProc, rawDue, wtOf, eligOf, hnj, hj2, hok]
    all_goals try simp [hK, hpz, hcz, hA, hB, hn, hvn, hc2]
    all_goals have hAlt := ‹cjA G (σ.vars "j" - nVJob G) < G.colours›
    all_goals try omega
    all_goals have hk1 : 1 < G.colours := (by omega)
    all_goals have hc2a := hbig.c2p hk1 _ 0 hple
    all_goals have hc2b := hbig.c2p hk1 G.vertices (@pos G (cjZ G (σ.vars "j" - nVJob G))) (le_refl _)
    all_goals have hc2c := hbig.c2B
    all_goals simp only [Nat.sub_zero] at hc2a
    all_goals try omega
    all_goals (simp only [c2, c1] at *; omega)
  · rintro σ hc
    have hc' := hc
    obtain ⟨hctx, hj1, hj2, -⟩ := hc
    have hpn : 0 < G.vertices := by
      rcases Nat.eq_zero_or_pos G.vertices with h | h
      · simp [nCJob, h] at hj2; omega
      · exact h
    have hpk : 0 < G.colours := by
      rcases Nat.eq_zero_or_pos G.colours with h | h
      · simp [nCJob, h] at hj2; omega
      · exact h
    refine ⟨hc', big hR, Nat.mod_lt _ hpn, Nat.mod_lt _ hpk, ?_⟩
    have hq : σ.vars "j" - nVJob G < G.colours * G.colours * G.vertices := by
      simp only [nCJob] at hj2; omega
    simp only [cjA]
    rw [Nat.div_div_eq_div_mul]
    exact (Nat.div_lt_iff_lt_mul (Nat.mul_pos hpn hpk)).mpr (by
      rw [show G.colours * (G.vertices * G.colours) = G.colours * G.colours * G.vertices by ring]
      exact hq)

/-! ### Edge jobs -/

/-- The state between an edge job's loading and its numbers. -/
def EDec (x : List ℕ) (G : Instance) (σ : Env) : Prop :=
  Ctx x G σ ∧ nVJob G + nCJob G ≤ σ.vars "j" ∧ σ.vars "j" < nJobs G ∧
    σ.vars "pu" = pos (G := G) (ejU G (σ.vars "j" - nVJob G - nCJob G)) ∧
    σ.vars "pw" = pos (G := G) (ejV G (σ.vars "j" - nVJob G - nCJob G)) ∧
    σ.vars "cu" = col (G := G) (ejU G (σ.vars "j" - nVJob G - nCJob G)) ∧
    σ.vars "cw" = col (G := G) (ejV G (σ.vars "j" - nVJob G - nCJob G))

theorem eLoad_spec (hR : Reads x G) :
    Spec (bnd x G)
      (fun σ => Ctx x G σ ∧ nVJob G + nCJob G ≤ σ.vars "j" ∧ σ.vars "j" < nJobs G) eLoad
      (fun σ σ' => EDec x G σ' ∧ Fr σ σ') 60 := by
  refine Spec.pre (P := fun σ => Ctx x G σ ∧ nVJob G + nCJob G ≤ σ.vars "j" ∧
      σ.vars "j" < nJobs G ∧ σ.vars "j" - nVJob G - nCJob G < nEJob G ∧
      ReadsB x G ∧ Big x G) ?_ ?_
  · run_vcg
    all_goals have hctx0 := ‹Ctx x G σ›
    all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hrk, hed, hK, hc1, hc2, hval, hM, hnc,
      hnkc, hnJ, hN, hW, hc3⟩ := ‹Ctx x G σ›
    all_goals obtain ⟨hoffB, htgtB, hcolB, hlenB, hblen⟩ := ‹ReadsB x G›
    all_goals have hbig := ‹Big x G›
    all_goals have hvn := hbig.vn_eq
    all_goals have hkk := hbig.kk_eq
    all_goals have hsm := hbig.small
    all_goals have hq := ‹σ.vars "j" - nVJob G - nCJob G < nEJob G›
    all_goals obtain ⟨heU, heV, hUlt, hVlt, hEe⟩ := edge_read hR hed hq
    all_goals have hnke : vn x * kk x = nVJob G := by rw [hvn, hkk]
    all_goals have hnJe : nJobs G = nVJob G + nCJob G + nEJob G := rfl
    all_goals have heU' : (σ.arrs "eu")[σ.vars "j" - nVJob G - nCJob G]?.getD 0
        = (ejU G (σ.vars "j" - nVJob G - nCJob G)) :=
      (by rw [← List.getD_eq_getElem?_getD]; exact heU)
    all_goals have heV' : (σ.arrs "ev")[σ.vars "j" - nVJob G - nCJob G]?.getD 0
        = (ejV G (σ.vars "j" - nVJob G - nCJob G)) :=
      (by rw [← List.getD_eq_getElem?_getD]; exact heV)
    all_goals have hrU : (σ.arrs "r")[ejU G (σ.vars "j" - nVJob G - nCJob G)]?.getD 0
        = @pos G (ejU G (σ.vars "j" - nVJob G - nCJob G)) :=
      (by rw [← List.getD_eq_getElem?_getD]; exact rank_read hR hrk hUlt)
    all_goals have hrV : (σ.arrs "r")[ejV G (σ.vars "j" - nVJob G - nCJob G)]?.getD 0
        = @pos G (ejV G (σ.vars "j" - nVJob G - nCJob G)) :=
      (by rw [← List.getD_eq_getElem?_getD]; exact rank_read hR hrk hVlt)
    all_goals have hpU := pos_le hR hUlt
    all_goals have hpV := pos_le hR hVlt
    all_goals have hcU := colr_eq_col hR hUlt
    all_goals have hcV := colr_eq_col hR hVlt
    all_goals have hrlen : (σ.arrs "r").length = G.vertices := by rw [hrk.1, hvn]
    all_goals have hoc : ∀ v, off x (G.vertices + 1 + 2 * ve x + v) = colr x v :=
      fun v => (by rw [← hvn]; exact off_col x v)
    all_goals have heulen := hed.2.1
    all_goals have hevlen := hed.2.2.1
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      all_goals simp [Fr, hn, hm, ha, htb, hcb, hk, hnk, hnke, hnc, hvn, hkk, body_off',
        heU', heV', hrU, hrV, hoc, hcU, hcV]
      all_goals try omega
    all_goals try simp [hn, hm, ha, htb, hcb, hk, hnk, hnke, hnc, hvn, hkk, body_off',
      heU', heV', hrU, hrV, hoc, hcU, hcV, hrlen]
    all_goals try omega
    all_goals have hnv : nVJob G = G.vertices * G.colours := rfl
    all_goals have hEle : nEJob G ≤ 2 * ve x := (by
      rw [← hEe, hed.1]; exact acc_length_le _ _)
    all_goals have hcUl := col_lt (G := G) hUlt
    all_goals have hcVl := col_lt (G := G) hVlt
    all_goals (simp only [hnv] at *; omega)
  · rintro σ ⟨hctx, hj1, hj2⟩
    exact ⟨hctx, hj1, hj2, by simp only [nJobs] at hj2; omega, readsB hR, big hR⟩

theorem eTail_spec (hR : Reads x G) :
    Spec (bnd x G) (EDec x G) eTail
      (fun σ σ' => Ctx x G σ' ∧ Fr σ σ' ∧ Raw G (σ.vars "j") σ') 80 := by
  refine Spec.pre (P := fun σ => EDec x G σ ∧ Big x G ∧
      σ.vars "j" - nVJob G - nCJob G < nEJob G) ?_ ?_
  · run_vcg
    all_goals have hctx0 : Ctx x G σ := (‹EDec x G σ›).1
    all_goals obtain ⟨hctx, hj1, hj2, hpu, hpw, hcu, hcw⟩ := ‹EDec x G σ›
    all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hrk, hed, hK, hc1, hc2, hval, hM, hnc,
      hnkc, hnJ, hN, hW, hc3⟩ := hctx
    all_goals have hbig := ‹Big x G›
    all_goals have hq := ‹σ.vars "j" - nVJob G - nCJob G < nEJob G›
    all_goals obtain ⟨-, -, hUlt, hVlt, -⟩ := edge_read hR hed hq
    all_goals obtain ⟨hclt, hcVl⟩ := Lax470956Proofs.Construction1Emit.edge_col_lt (G := G) hq
    all_goals have hk1 : 1 < G.colours := (by omega)
    all_goals have hc3' := hc3 hk1
    all_goals have hpU := pos_le hR hUlt
    all_goals have hpV := pos_le hR hVlt
    all_goals have hKp := hbig.Kp _ hpV
    all_goals have hKd := hbig.Kd _ (@pos G (ejU G (σ.vars "j" - nVJob G - nCJob G))) hpV
    all_goals have hc2d := hbig.c2p hk1 _ (@pos G (ejU G (σ.vars "j" - nVJob G - nCJob G))) hpV
    all_goals have hc3B := hbig.c3B hk1
    all_goals have hpe := hbig.pe _ (Nat.le_of_lt hcVl)
    all_goals have hsm := hbig.small
    all_goals have hc2c := hbig.c2B
    all_goals have hnj1 : ¬ σ.vars "j" < nVJob G := (by omega)
    all_goals have hnj2 : ¬ σ.vars "j" < nVJob G + nCJob G := (by omega)
    · refine ⟨?_, ?_, ?_⟩
      · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
      · simp [Fr]
      · have hok : EJobOk G (σ.vars "j" - nVJob G - nCJob G) := hq
        simp [Raw, rawProc, rawDue, wtOf, eligOf, hnj1, hnj2, hok, hK, hpu, hpw, hcu, hcw,
          hc2, hc3', pairIdx, Nat.choose_two_right]
    all_goals try simp [hK, hpu, hpw, hcu, hcw, hc2, hc3']
    all_goals try omega
    all_goals (simp only [c2, c1] at *; omega)
  · rintro σ he
    have he' := he
    obtain ⟨-, hj1, hj2, -⟩ := he
    exact ⟨he', big hR, by simp only [nJobs] at hj2; omega⟩

/-! ### The clamp -/

/-- The raw times of a job stay below the bound. -/
lemma raw_lt (hR : Reads x G) {j : ℕ} (hj : j < nJobs G) :
    rawProc G j < bnd x G ∧ rawDue G j < bnd x G := by
  have hbig := big hR
  have hsm := hbig.small
  by_cases h1 : j < nVJob G
  · have hpk : 0 < G.colours := by
      rcases Nat.eq_zero_or_pos G.colours with h | h
      · simp [nVJob, h] at h1
      · exact h
    have hz : vjVert G j < G.vertices := (Nat.div_lt_iff_lt_mul hpk).mpr h1
    have hKp := hbig.Kp _ (pos_le hR hz)
    simp only [rawProc, rawDue, h1, if_true, K]
    split_ifs <;> constructor <;> omega
  · by_cases h2 : j < nVJob G + nCJob G
    · simp only [rawProc, rawDue, h1, h2, if_true, if_false, K]
      by_cases hok : CJobOk G (j - nVJob G)
      · have hz := hok.2.2.1
        have hB := hok.2.1
        have hA : cjA G (j - nVJob G) < G.colours := lt_trans hok.1 hB
        have hKp := hbig.Kp _ (pos_le hR hz)
        have hKn := hbig.Kp _ (le_refl G.vertices)
        have hKd := hbig.Kd G.vertices (@pos G (cjZ G (j - nVJob G))) (le_refl _)
        simp only [hok, if_true]
        split_ifs <;> constructor <;> omega
      · simp only [hok, if_false]
        constructor <;> omega
    · have hq : j - nVJob G - nCJob G < nEJob G := by simp only [nJobs] at hj; omega
      have hok : EJobOk G (j - nVJob G - nCJob G) := hq
      obtain ⟨hclt, hcVl⟩ := Lax470956Proofs.Construction1Emit.edge_col_lt (G := G) hq
      have hVlt : ejV G (j - nVJob G - nCJob G) < G.vertices := by
        rw [ejV, List.getElem?_eq_getElem hq]; simp
      have hKp := hbig.Kp _ (pos_le hR hVlt)
      have hKd := hbig.Kd _ (@pos G (ejU G (j - nVJob G - nCJob G))) (pos_le hR hVlt)
      simp only [rawProc, rawDue, h1, h2, if_false, hok, if_true, K]
      constructor <;> omega

/-- The numbers a pass writes for job `j` are in the scalars. -/
def Done (G : Instance) (j : ℕ) (σ' : Env) : Prop :=
  σ'.vars "P" = procOf G j ∧ σ'.vars "D" = dueOf G j ∧ σ'.vars "Wt" = wtOf G j ∧
    eligOf G j = [σ'.vars "E1", σ'.vars "E2"].take (σ'.vars "EL") ∧ σ'.vars "EL" ≤ 2

theorem clamp_spec (hR : Reads x G) :
    Spec (bnd x G)
      (fun σ => Ctx x G σ ∧ σ.vars "j" < nJobs G ∧ Raw G (σ.vars "j") σ) clamp
      (fun σ σ' => Ctx x G σ' ∧ Fr σ σ' ∧ Done G (σ.vars "j") σ') 40 := by
  refine Spec.pre (P := fun σ => Ctx x G σ ∧ Raw G (σ.vars "j") σ ∧
      σ.vars "rp" < bnd x G ∧ σ.vars "rd" < bnd x G ∧ 2 < bnd x G) ?_ ?_
  · run_vcg
    all_goals have hctx0 := ‹Ctx x G σ›
    all_goals obtain ⟨hrp, hrd, hwt, hel, hel2⟩ := ‹Raw G (σ.vars "j") σ›
    all_goals try
      (refine ⟨?_, ?_, ?_⟩
       · repeat' (first | exact hctx0 | refine Ctx.setVar ?_ _ _ (by decide))
       · simp [Fr]
       · simp_all [Done, procOf, dueOf] <;> omega)
    all_goals try simp_all
    all_goals try omega
  · rintro σ ⟨hctx, hj, hraw⟩
    obtain ⟨h1, h2⟩ := raw_lt hR hj
    have hsm := (big hR).small
    exact ⟨hctx, hraw, by rw [hraw.1]; exact h1, by rw [hraw.2.1]; exact h2, by omega⟩

/-! ### Everything about job `j` -/

theorem info_spec (hR : Reads x G) :
    Spec (bnd x G) (fun σ => Ctx x G σ ∧ σ.vars "j" < nJobs G) info
      (fun σ σ' => Ctx x G σ' ∧ Fr σ σ' ∧ Done G (σ.vars "j") σ') 300 := by
  have hbig := big hR
  have hsm := hbig.small
  have hnJe : nJobs G = nVJob G + nCJob G + nEJob G := rfl
  have hnk : ∀ σ : Env, Ctx x G σ → σ.vars "nk" = nVJob G := fun σ h => by
    rw [h.1.2.2.2.2.2.2, hbig.vn_eq, hbig.kk_eq]
  have hnkc : ∀ σ : Env, Ctx x G σ → σ.vars "nkc" = nVJob G + nCJob G :=
    fun σ h => h.2.2.2.2.2.2.2.2.2.1
  run_vcg [vDecode_spec hR, vBody_spec hR, cDecode_spec hR, cBody_spec hR, eLoad_spec hR,
    eTail_spec hR, clamp_spec hR]
  all_goals have e1 := hnk σ ‹Ctx x G σ›
  all_goals have e2 := hnkc σ ‹Ctx x G σ›
  all_goals try omega
  all_goals try simp only [Fr, VDec] at *
  all_goals try (refine ⟨by assumption, by omega⟩)
  all_goals try (refine ⟨by assumption, by omega, by omega⟩)
  all_goals try (simp_all; done)
  all_goals try (simp_all; omega)

end Lax470956Proofs.Construction1Info
