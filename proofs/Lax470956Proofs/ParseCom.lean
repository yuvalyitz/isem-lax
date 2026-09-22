import Lax470956Proofs.ParseMain

/-!
The parser's program, whole.
-/

namespace Lax470956Proofs.ParseCom

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956Proofs.ParseModel Lax470956Proofs.ParseSem Lax470956Proofs.ParseScan
open Lax470956Proofs.ParseNames Lax470956Proofs.ParseMain Lax470956Proofs.Theorem2Assembly

variable {B : ℕ} {y : List ℕ}

def tail : Com :=
  .ite (.eq (V "ph") (.lit 4))
    (.seq (set "ok" 1) (.seq outerLoop (.ite (.eq (V "ok") (.lit 1)) emitAll .skip)))
    .skip

/-- What the scan leaves behind. -/
def Scanned (y : List ℕ) (σ : Env) : Prop :=
  SInv y σ ∧ σ.vars "p" = y.length ∧ σ.out = [] ∧
    (σ.arrs "nm").length = y.length + 1 ∧ (σ.arrs "ap").length = y.length + 1

lemma nctx_of_scanned {σ : Env} (h : Scanned y σ) :
    NCtx (vsAt y) (y.length + 1) σ ∧ (σ.arrs "sg").length = y.length + 1 ∧
      (∀ j < (vsAt y).length, (σ.arrs "sg").getD j 0 = (ssAt y).getD j 0) ∧
      σ.vars "C" = (stAt y y.length).done.length ∧ σ.vars "ph" = (stAt y y.length).ph := by
  obtain ⟨⟨-, -, -, hl1, hl2, hR⟩, hp, -, -, -⟩ := h
  rw [hp] at hR
  refine ⟨⟨by rw [hR.k, vsAt, List.length_map], hl1, fun i hi => ?_⟩, hl2, fun j hj => ?_, hR.C, hR.ph⟩
  · rw [vsAt, List.length_map] at hi
    rw [hR.vr i hi, vsAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases (flat (stAt y y.length))[i]? <;> rfl
  · rw [vsAt, List.length_map] at hj
    rw [hR.sg j hj, ssAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases (flat (stAt y y.length))[j]? <;> rfl

lemma parse_word (h4 : (stAt y y.length).ph = 4) (hc : ∀ v ∈ vsAt y, (vsAt y).count v ≤ 4) :
    parse y = word (vsAt y) (ssAt y) (stAt y y.length).done.length := by
  rw [stAt_length] at h4 ⊢
  obtain ⟨hv, hs⟩ := accepted_flat h4
  rw [hv] at hc
  rw [parse, parseBits]
  simp only [h4, true_and]
  rw [if_pos hc, hv, hs]

lemma parse_nil_of_count (h4 : (stAt y y.length).ph = 4)
    (hc : ¬ ∀ v ∈ vsAt y, (vsAt y).count v ≤ 4) : parse y = [] := by
  rw [stAt_length] at h4
  obtain ⟨hv, hs⟩ := accepted_flat h4
  rw [hv] at hc
  rw [parse, parseBits]
  simp only [h4, true_and]
  rw [if_neg hc]

lemma parse_nil_of_phase (h4 : (stAt y y.length).ph ≠ 4) : parse y = [] := by
  rw [stAt_length] at h4
  rw [parse, parseBits]
  exact if_neg (fun h => h4 h.1)

theorem tail_spec (hB : y.length + 10 < B) (K2 KE : ℕ)
    (hK2 : ((44 * (vsAt y).length + 6) + 40 + 4) * (vsAt y).length + 6 = K2)
    (hKE : 24 * (vsAt y).length + 6 = KE) :
    Spec B (fun σ => Scanned y σ) tail (fun _ σ' => σ'.out = parse y) (K2 + KE + 30) := by
  have hlen := vsAt_length_le (y := y)
  have hnw := noWrite_outerLoop
  have ho : Spec B _ outerLoop _ K2 := hK2 ▸ (outerLoop_spec (B := B) (vs := vsAt y)
    (y.length + 1) _ (by omega) (by omega) (vsAt_lt (by omega)) rfl)
  have he := emitAll_spec (B := B) (vs := vsAt y) (ss := ssAt y) (y.length + 1)
    (stAt y y.length).done.length KE (by omega) (by omega) ssAt_le
    (by have := size_stAt (y := y) y.length; simp only [ParseScan.size] at this; omega) hKE
  run_vcg [ho.frame, he]
  all_goals have hS := ‹Scanned y σ›
  all_goals obtain ⟨hctx, hsl, hsg, hC, hph⟩ := nctx_of_scanned hS
  all_goals have hph5 : (stAt y y.length).ph ≤ 5 := ph_run_le _
  all_goals try omega
  all_goals try
    (obtain ⟨hN, hfv, hfa, -, hfo⟩ := ‹Named _ _ _ ∧ _›
     have hCw := hfv "C" (by simp [wvars_outerLoop])
     have hsgw := hfa "sg" (by simp [warrs_outerLoop])
     have houtw := hfo hnw
     simp only [Env.setVar, String.reduceEq, ↓reduceIte] at hCw hsgw houtw)
  · refine Eq.trans ‹_ = word (vsAt y) (ssAt y) _› ?_
    exact (parse_word (by omega) (hN.2.2.2.2.2.mp ‹_›)).symm
  · rw [houtw, hS.2.2.1]
    exact (parse_nil_of_count (by omega) (fun h => ‹¬ _› (hN.2.2.2.2.2.mpr h))).symm
  · rw [hS.2.2.1]
    exact (parse_nil_of_phase (by omega)).symm
  · exact ⟨by simpa [NCtx, Env.setVar] using hctx, by simpa [Env.setVar] using hS.2.2.2.1,
      by simpa [Env.setVar] using hS.2.2.2.2, by simp [Env.setVar]⟩
  · have := hN.2.2.2.2.1; omega
  · exact ⟨⟨hN, by rw [hsgw]; exact hsl, fun j hj => by rw [hsgw]; exact hsg j hj⟩,
      by rw [hCw]; exact hC, by rw [houtw]; exact hS.2.2.1⟩

/-! ### The whole program -/

def scanInit : Com :=
  .seq (set "ph" 0) (.seq (set "n" 0) (.seq (set "h" 0) (.seq (set "C" 0) (set "k" 0))))

def com : Com := .seq ReadAll.readAll (.seq scanInit (.seq scanLoop tail))

/-- What reading the word leaves behind. -/
def Loaded (y : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ σ.out = [] ∧
    (σ.arrs "vr").length = y.length + 1 ∧ (σ.arrs "sg").length = y.length + 1 ∧
    (σ.arrs "nm").length = y.length + 1 ∧ (σ.arrs "ap").length = y.length + 1

theorem scanInit_spec (hB : y.length + 10 < B) :
    Spec B (fun σ => Loaded y σ) scanInit
      (fun _ σ' => SInv y (σ'.setVar "p" 0) ∧ Loaded y σ') 12 := by
  run_vcg
  all_goals try omega
  obtain ⟨ha, hL, hout, h1, h2, h3, h4⟩ := ‹Loaded y σ›
  refine ⟨⟨ha, hL, by simp [Env.setVar], h1, h2, ?_⟩, ha, hL, hout, h1, h2, h3, h4⟩
  have h0 : stAt y 0 = init := by simp [stAt, bitsOf]
  simp only [Env.setVar, String.reduceEq, ↓reduceIte, h0]
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun i hi => by simp [flat, init, litsOf] at hi,
    fun i hi => by simp [flat, init, litsOf] at hi⟩

lemma warrs_scanLoop : ∀ x ∈ scanLoop.warrs, x ∈ ["vr", "sg"] := by
  simp [scanLoop, scanBody, dispatch, phase1, phase3, Com.warrs]

lemma noWrite_scanLoop : scanLoop.NoWrite := by
  simp [scanLoop, scanBody, dispatch, phase1, phase3, Com.NoWrite]

lemma warrs_readAll : ∀ x ∈ ReadAll.readAll.warrs, x ∈ ["a"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.warrs]

def K2 (y : List ℕ) : ℕ := ((44 * (vsAt y).length + 6) + 40 + 4) * (vsAt y).length + 6
def KE (y : List ℕ) : ℕ := 24 * (vsAt y).length + 6

/-- The cost of the whole program, in IMP+ units. -/
def Kc (y : List ℕ) : ℕ := 12 * y.length + 74 * y.length + K2 y + KE y + 100

theorem com_spec (hy : ∀ v ∈ y, v < B) (hB : y.length + 10 < B) :
    Spec B (fun σ => σ.inp = y.length :: y ∧ σ.out = [] ∧ (σ.arrs "a").length = y.length ∧
        (σ.arrs "vr").length = y.length + 1 ∧ (σ.arrs "sg").length = y.length + 1 ∧
        (σ.arrs "nm").length = y.length + 1 ∧ (σ.arrs "ap").length = y.length + 1)
      com (fun _ σ' => σ'.out = parse y) (Kc y) := by
  intro σ ⟨hinp, hout, hla, h1, h2, h3, h4⟩
  obtain ⟨σ1, hrun1, ⟨hL, ha, hout1, -⟩, -, hfa, -, -⟩ :=
    (ReadAll.readAll_spec hy (by omega)).frame σ ⟨hinp, hout, hla⟩
  have hfar : ∀ x, x ≠ "a" → σ1.arrs x = σ.arrs x := fun x hx =>
    hfa x (fun hm => hx (by simpa using warrs_readAll x hm))
  obtain ⟨σ2, hrun2, hS2, hL2⟩ := scanInit_spec hB σ1
    ⟨ha, hL, hout1, by rw [hfar _ (by decide)]; exact h1, by rw [hfar _ (by decide)]; exact h2,
      by rw [hfar _ (by decide)]; exact h3, by rw [hfar _ (by decide)]; exact h4⟩
  obtain ⟨σ3, hrun3, ⟨hS3, hp3⟩, -, hfa3, -, hfo3⟩ := (scanLoop_spec hy (by omega)).frame σ2 hS2
  have hfa3' : ∀ x, x ≠ "vr" → x ≠ "sg" → σ3.arrs x = σ2.arrs x := fun x hx1 hx2 =>
    hfa3 x (fun hm => by
      have := warrs_scanLoop x hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl
      · exact hx1 rfl
      · exact hx2 rfl)
  obtain ⟨σ4, hrun4, hout4⟩ := tail_spec hB (K2 y) (KE y) rfl rfl σ3
    ⟨hS3, hp3, by rw [hfo3 noWrite_scanLoop]; exact hL2.2.2.1,
      by rw [hfa3' _ (by decide) (by decide)]; exact hL2.2.2.2.2.2.1,
      by rw [hfa3' _ (by decide) (by decide)]; exact hL2.2.2.2.2.2.2⟩
  exact ⟨σ4, (Run.seq hrun1 (Run.seq hrun2 (Run.seq hrun3 hrun4))).mono (by unfold Kc; omega),
    hout4⟩

end Lax470956Proofs.ParseCom
