import Lax470956Proofs.ParseNames

/-!
The parser, assembled: read, scan, name, write.
-/

namespace Lax470956Proofs.ParseMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956Proofs.ParseModel Lax470956Proofs.ParseSem Lax470956Proofs.ParseScan
open Lax470956Proofs.ParseNames Lax470956Proofs.Theorem2Assembly

variable {B : ℕ} {vs ss : List ℕ}

/-! ### Writing the Word -/

def emitBody : Com :=
  .seq (.write (.get "nm" (V "q"))) (.seq (.write (.get "sg" (V "q")))
    (.seq (.write (.get "ap" (V "q"))) (bump "q")))

def emitLoop : Com := .seq (set "q" 0) (.while (.lt (V "q") (V "k")) emitBody)

def EInv (vs ss : List ℕ) (M : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Named vs M σ ∧ (σ.arrs "sg").length = M ∧ (∀ j < vs.length, (σ.arrs "sg").getD j 0 = ss.getD j 0) ∧
    σ.vars "q" ≤ vs.length ∧
    σ.out = out0 ++ (List.range (σ.vars "q")).flatMap
      fun k => [nameOf vs k, ss.getD k 0, appOf vs k]

theorem emitBody_spec (M : ℕ) (out0 : List ℕ) (hM : vs.length < M) (hB : M + 9 < B)
    (hss : ∀ j < vs.length, ss.getD j 0 ≤ 1) :
    Spec B (fun σ => EInv vs ss M out0 σ ∧ σ.vars "q" < vs.length) emitBody
      (fun σ σ' => EInv vs ss M out0 σ' ∧ σ'.vars "q" = σ.vars "q" + 1) 20 := by
  run_vcg
  all_goals obtain ⟨⟨⟨hk, hlen, hvr⟩, hn1, hn2, hcell, hok1, hok⟩, hs1, hsg, hqle, hout⟩ :=
    ‹EInv vs ss M out0 σ›
  all_goals have hqlt := ‹σ.vars "q" < vs.length›
  all_goals have hc := hcell _ hqlt
  all_goals have hsq := hsg _ hqlt
  all_goals have hsl := hss _ hqlt
  all_goals have hnl := nameOf_lt (vs := vs) hqlt
  all_goals have hal := appOf_le vs (σ.vars "q")
  all_goals try omega
  all_goals simp only [EInv, Named, NCtx, Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals first
    | omega
    | (rw [hc.1]; omega)
    | (rw [hc.2]; omega)
    | (rw [hsq]; omega)
    | (refine ⟨⟨⟨⟨hk, hlen, hvr⟩, hn1, hn2, hcell, hok1, hok⟩, hs1, hsg, by omega, ?_⟩, trivial⟩
       rw [hout, hc.1, hc.2, hsq, List.range_succ, List.flatMap_append]
       simp)

theorem emitLoop_ghost (M : ℕ) (out0 : List ℕ) (hM : vs.length < M) (hB : M + 9 < B)
    (hss : ∀ j < vs.length, ss.getD j 0 ≤ 1) :
    Spec B (fun σ => EInv vs ss M out0 (σ.setVar "q" 0)) emitLoop
      (fun _ σ' => EInv vs ss M out0 σ' ∧ σ'.vars "q" = vs.length) ((20 + 4) * vs.length + 6) :=
  Spec.forRangeZero "q" "k" (EInv vs ss M out0) vs.length 20 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.1.1.1) (emitBody_spec M out0 hM hB hss)

/-- What the writer needs: the names, and the signs. -/
def Ready (vs ss : List ℕ) (M : ℕ) (σ : Env) : Prop :=
  Named vs M σ ∧ (σ.arrs "sg").length = M ∧ ∀ j < vs.length, (σ.arrs "sg").getD j 0 = ss.getD j 0

theorem emitLoop_spec (M : ℕ) (hM : vs.length < M) (hB : M + 9 < B)
    (hss : ∀ j < vs.length, ss.getD j 0 ≤ 1) :
    Spec B (fun σ => Ready vs ss M σ) emitLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range vs.length).flatMap
        fun k => [nameOf vs k, ss.getD k 0, appOf vs k]) (24 * vs.length + 6) := by
  intro σ ⟨hN, h1, h2⟩
  obtain ⟨σ', hrun, hI, hq⟩ := emitLoop_ghost M σ.out hM hB hss σ
    ⟨by simpa [Named, NCtx, Env.setVar] using hN, by simpa [Env.setVar] using h1,
      by simpa [Env.setVar] using h2, by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ', hrun, ?_⟩
  show σ'.out = _
  rw [hI.2.2.2.2, hq]

def emitAll : Com := .seq (.write (V "k")) (.seq (.write (V "C")) emitLoop)

theorem emitAll_spec (M C0 KE : ℕ) (hM : vs.length < M) (hB : M + 9 < B)
    (hss : ∀ j < vs.length, ss.getD j 0 ≤ 1) (hC0 : C0 < M) (hKE : 24 * vs.length + 6 = KE) :
    Spec B (fun σ => Ready vs ss M σ ∧ σ.vars "C" = C0 ∧ σ.out = []) emitAll
      (fun _ σ' => σ'.out = word vs ss C0) (KE + 10) := by
  have he : Spec B _ emitLoop _ KE := hKE ▸ (emitLoop_spec (B := B) M hM hB hss)
  run_vcg [he]
  all_goals obtain ⟨⟨⟨hk, hlen, hvr⟩, hrest⟩, h1, h2⟩ := ‹Ready vs ss M σ›
  all_goals try omega
  · simp_all [word]
  · exact ⟨⟨⟨hk, hlen, hvr⟩, hrest⟩, h1, h2⟩

/-! ### From the Scan to the Names -/

open Lax429075.CNF Lax434930.PolynomialTime

lemma flat_step (s : St) (b : Bool) : ∀ l ∈ flat (step s b), l ∈ flat s ∨ l.index = s.n := by
  obtain ⟨ph, n, d, c⟩ := s
  intro l hl
  match ph with
  | 0 => cases b <;> simp_all [step, flat]
  | 1 =>
      by_cases h : c.length < 3 <;> cases b <;>
        simp only [step, h, flat, if_true, if_false, List.append_nil] at hl ⊢ <;>
        first
          | (simp_all; done)
          | (left; simpa [litsOf] using hl)
  | 2 => cases b <;> simp_all [step, flat]
  | 3 =>
      simp only [step, flat, List.mem_append, List.mem_singleton] at hl ⊢
      rcases hl with hl | hl | rfl
      · exact Or.inl (Or.inl hl)
      · exact Or.inl (Or.inr hl)
      · exact Or.inr rfl
  | k + 4 => simp_all [step, flat]

lemma index_le (w : Word) : ∀ l ∈ flat (run init w), l.index ≤ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [init, flat, litsOf]
  | append_singleton u b ih =>
      intro l hl
      rw [run_append] at hl
      simp only [run_cons, run_nil, List.length_append, List.length_singleton] at hl ⊢
      rcases flat_step _ _ l hl with h | h
      · have := ih l h; omega
      · have h1 := size_run u
        have h2 : (run init u).n ≤ ParseScan.size (run init u) := by simp [ParseScan.size]
        omega

/-- The variables and the signs the scan has collected. -/
def vsAt (y : List ℕ) : List ℕ := (flat (stAt y y.length)).map Literal.index
def ssAt (y : List ℕ) : List ℕ :=
  (flat (stAt y y.length)).map fun l => if l.positive then 1 else 0

variable {y : List ℕ}

lemma stAt_length : stAt y y.length = run init (bitsOf y) := by rw [stAt, List.take_length]

lemma vsAt_length_le : (vsAt y).length ≤ y.length := by
  have := size_stAt (y := y) y.length
  simp only [vsAt, List.length_map, ParseScan.size] at this ⊢
  omega

lemma vsAt_lt (hB : y.length + 9 < B) : ∀ v ∈ vsAt y, v < B := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
  rw [stAt_length] at hl
  have := index_le _ l hl
  simp only [bitsOf, List.length_map] at this
  omega

lemma ssAt_le : ∀ j < (vsAt y).length, (ssAt y).getD j 0 ≤ 1 := by
  intro j _
  simp only [ssAt, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (flat (stAt y y.length))[j]? with
  | none => simp
  | some l => simp only [Option.map_some, Option.getD_some]; split_ifs <;> omega

lemma accepted_flat (h : (run init (bitsOf y)).ph = 4) :
    vsAt y = vsOf (run init (bitsOf y)).done ∧ ssAt y = ssOf (run init (bitsOf y)).done := by
  have hcur := (run_inv _ (by omega)).1.2.2.1 (Or.inr h)
  simp only [vsAt, ssAt, stAt_length, flat, hcur, List.append_nil, vsOf, ssOf, and_self]

/-- **The parser.** -/
def parse (y : List ℕ) : List ℕ := parseBits (bitsOf y)

end Lax470956Proofs.ParseMain
