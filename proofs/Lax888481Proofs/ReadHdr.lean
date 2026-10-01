import Lax888481Proofs.ReadAll
import Lax888481.InstanceEncoding

/-!
Reading a word whose length the word itself declares.

The polynomial-time predicate hands a program its input preceded by its length, but a
parameterized statement hands it the word alone. A scheduling word says how long it is —
two header entries, three arrays of one number per job, `n+1` offsets whose last entry
says how long the target array is, and a threshold — so the program reads it in three
goes, computing the next bound from what it has read.
-/

namespace Lax888481Proofs.ReadHdr

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax888481Proofs.ReadAll (readBody)
open Lax888481.InstanceEncoding

abbrev V (s : String) : Expr := .var s
abbrev lit (n : ℕ) : Expr := .lit n
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev set (s : String) (e : Expr) : Com := .assign s e

variable {B : ℕ} {y : List ℕ}

/-! ### Evaluating an Expression -/

lemma evalB_lit {σ : Env} {v : ℕ} (h : v < B) : (lit v).evalB B σ = some v := fit_self h

lemma evalB_var {σ : Env} {y : String} (h : σ.vars y < B) :
    (V y).evalB B σ = some (σ.vars y) := fit_self h

lemma evalB_add {σ : Env} {e f : Expr} {a b : ℕ} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) (h : a + b < B) : (add e f).evalB B σ = some (a + b) := by
  simp only [Expr.evalB, he, hf, Option.bind_some, Bop.apply_add]; exact fit_self h

lemma evalB_sub {σ : Env} {e f : Expr} {a b : ℕ} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) (h : a - b < B) : (sub e f).evalB B σ = some (a - b) := by
  simp only [Expr.evalB, he, hf, Option.bind_some, Bop.apply_sub]; exact fit_self h

lemma evalB_mul {σ : Env} {e f : Expr} {a b : ℕ} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) (h : a * b < B) : (mul e f).evalB B σ = some (a * b) := by
  simp only [Expr.evalB, he, hf, Option.bind_some, Bop.apply_mul]; exact fit_self h

lemma evalB_getE {σ : Env} {nm : String} {e : Expr} {i v : ℕ}
    (he : e.evalB B σ = some i) (hv : v < B)
    (hlen : i < (σ.arrs nm).length) (hval : (σ.arrs nm).getD i 0 = v) :
    (Expr.get nm e).evalB B σ = some v := by
  have h1 : (σ.arrs nm)[i]? = some v := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen] at hval
    rw [List.getElem?_eq_getElem hlen]
    simpa using hval
  simp [Expr.evalB, he, h1, fit_self hv]

/-- Reading `nm[y]` when the value and the index are both in range. -/
lemma evalB_getvar {σ : Env} {nm y : String} {i v : ℕ} (hi : i < B) (hv : v < B)
    (hy : σ.vars y = i) (hlen : i < (σ.arrs nm).length)
    (hval : (σ.arrs nm).getD i 0 = v) :
    (Expr.get nm (Expr.var y)).evalB B σ = some v := by
  have h1 : (σ.arrs nm)[i]? = some v := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen] at hval
    rw [List.getElem?_eq_getElem hlen]
    simpa using hval
  simp [Expr.evalB, hy, fit_self hi, h1, fit_self hv]

/-- Read on until `rt` reaches `L`. -/
def readUpTo : Com := .while (.lt (.var "rt") (.var "L")) readBody

/-- The state of a partial read. -/
def UInv (y : List ℕ) (L : ℕ) (σ : Env) : Prop :=
  σ.vars "L" = L ∧ σ.vars "rt" ≤ L ∧ (σ.arrs "a").length = y.length ∧
    (∀ i < σ.vars "rt", (σ.arrs "a").getD i 0 = y.getD i 0) ∧
    σ.inp = y.drop (σ.vars "rt") ∧ σ.out = []

theorem readBody_spec' (L : ℕ) (hL : L ≤ y.length) (hy : ∀ v ∈ y, v < B)
    (hB : y.length + 1 < B) :
    Spec B (fun σ => UInv y L σ ∧ σ.vars "rt" < L) readBody
      (fun σ σ' => UInv y L σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 8 := by
  refine Spec.pre (P := fun σ => UInv y L σ ∧ σ.vars "rt" < L ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < B ∧ σ.vars "rt" < (σ.arrs "a").length) ?_ ?_
  · run_vcg
    · obtain ⟨hLv, hle, hlen, hcell, hinp, hout⟩ := ‹UInv y L σ›
      have htlt := ‹σ.vars "rt" < L›
      have hidx : σ.vars "rt" < (σ.arrs "a").length := by omega
      simp only [UInv]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hLv
      · omega
      · exact hlen
      · intro i hi
        rcases Nat.lt_or_ge i (σ.vars "rt") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell i h
        · have hylt : σ.vars "rt" < y.length := by omega
          have hie : i = σ.vars "rt" := by omega
          subst hie
          rw [hinp]
          simp [hylt, List.head?_drop, List.getElem?_set, hidx]
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
    refine ⟨hI, ht, hne, ?_, by have := hI.2.2.1; omega⟩
    rcases hh : σ.inp with _ | ⟨u, rest⟩
    · exact absurd hh hne
    · have : u ∈ y.drop (σ.vars "rt") := by rw [← hinp, hh]; exact List.mem_cons_self
      exact hy u (List.mem_of_mem_drop this)

theorem readUpTo_spec (L : ℕ) (hL : L ≤ y.length) (hy : ∀ v ∈ y, v < B)
    (hB : y.length + 1 < B) :
    Spec B (UInv y L) readUpTo (fun _ σ' => UInv y L σ' ∧ σ'.vars "rt" = L)
      (12 * L + 4) :=
  Spec.forRange "rt" "L" (UInv y L) L 8 (12 * L + 4)
    (fun _ h => by have := h.2.1; omega) (fun _ h => by rw [h.1]; omega)
    (fun _ h => h.1) (fun _ h => h.2.1) (readBody_spec' L hL hy hB)
    (fun _ h => h) (fun _ _ => by
      have : (8 + 4) * (L - 0) + 4 ≤ 12 * L + 4 := by omega
      exact le_trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4) (by omega))

/-! ### Reading a Scheduling Word -/

/-- Read the two header entries, then the three arrays and the offsets, then the target
array and the threshold. -/
def readWord : Com :=
  .seq (set "rt" (lit 0))
    (.seq (set "L" (lit 2))
      (.seq readUpTo
        (.seq (set "n" (.get "a" (lit 0)))
          (.seq (set "L" (add (lit 3) (mul (lit 4) (V "n"))))
            (.seq readUpTo
              (.seq (set "rv" (.get "a" (add (lit 2) (mul (lit 4) (V "n")))))
                (.seq (set "L" (add (add (V "L") (V "rv")) (lit 1)))
                  readUpTo)))))))

lemma UInv.setV {L : ℕ} {σ : Env} (h : UInv y L σ) {z : String} (h1 : z ≠ "L")
    (h2 : z ≠ "rt") (v : ℕ) : UInv y L (σ.setVar z v) := by
  refine ⟨by simp only [Env.setVar, if_neg h1.symm]; exact h.1,
    by simp only [Env.setVar, if_neg h2.symm]; exact h.2.1, h.2.2.1, ?_, ?_, h.2.2.2.2.2⟩
  · simp only [Env.setVar, if_neg h2.symm]; exact h.2.2.2.1
  · simp only [Env.setVar, if_neg h2.symm]; exact h.2.2.2.2.1

lemma uinv_step {L L' : ℕ} {σ : Env} (h : UInv y L σ) (hrt : σ.vars "rt" = L)
    (hLL : L ≤ L') : UInv y L' (σ.setVar "L" L') := by
  refine ⟨by simp [Env.setVar], by simp [Env.setVar, hrt]; omega,
    by simpa [Env.setVar] using h.2.2.1, ?_, ?_, ?_⟩
  · intro i hi; simp only [Env.setVar] at hi ⊢; exact h.2.2.2.1 i hi
  · simpa [Env.setVar] using h.2.2.2.2.1
  · simpa [Env.setVar] using h.2.2.2.2.2

theorem readWord_spec (n T : ℕ) (hy : ∀ v ∈ y, v < B) (hB : y.length + 1 < B)
    (hjc : jobCount y = n) (hoff : y.getD (2 + 4 * n) 0 = T)
    (hlen : y.length = 3 + 4 * n + T + 1) :
    Spec B (fun σ => σ.inp = y ∧ σ.out = [] ∧ (σ.arrs "a").length = y.length)
      readWord
      (fun _ σ' => σ'.arrs "a" = y ∧ σ'.out = [] ∧ σ'.inp = [] ∧
        σ'.vars "L" = y.length ∧ σ'.vars "rt" = y.length)
      (24 * y.length + 62) := by
  intro σ ⟨hinp, hout, hal⟩
  have hnB : n < B := by
    have : n = y.getD 0 0 := by rw [← hjc]; rfl
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · omega
    · have hm : y.getD 0 0 ∈ y := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _
      have := hy _ hm; omega
  have hTB : T < B := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · omega
    · have hm : y.getD (2 + 4 * n) 0 ∈ y := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _
      rw [hoff] at hm
      exact hy _ hm
  -- phase one
  set σ0 := (σ.setVar "rt" 0).setVar "L" 2 with hσ0
  have hrun0a : Run B (set "rt" (lit 0)) σ (σ.setVar "rt" 0) 2 :=
    (Run.assign (evalB_lit (show (0 : ℕ) < B by omega))).mono (by simp [Expr.size])
  have hrun0b : Run B (set "L" (lit 2)) (σ.setVar "rt" 0) σ0 2 :=
    (Run.assign (evalB_lit (show (2 : ℕ) < B by omega))).mono (by simp [Expr.size])
  have hU0 : UInv y 2 σ0 := by
    refine ⟨by simp [hσ0, Env.setVar], by simp [hσ0, Env.setVar], by
      simp [hσ0, Env.setVar, hal], ?_, ?_, ?_⟩
    · intro i hi; simp [hσ0, Env.setVar] at hi
    · simp [hσ0, Env.setVar, hinp]
    · simp [hσ0, Env.setVar, hout]
  obtain ⟨σ1, hrun1, hU1, hrt1⟩ := readUpTo_spec (y := y) 2 (by omega) hy hB σ0 hU0
  -- read the number of jobs
  have ha0 : (σ1.arrs "a").getD 0 0 = n := by
    rw [hU1.2.2.2.1 0 (by omega), ← hjc]; rfl
  have hev0 : (Expr.get "a" (lit 0)).evalB B σ1 = some n := by
    refine evalB_getE (fit_self (show (0 : ℕ) < B by omega)) (by omega) ?_ ha0
    have := hU1.2.2.1; omega
  set σ2 := σ1.setVar "n" n with hσ2
  have hrun2 : Run B (set "n" (.get "a" (lit 0))) σ1 σ2 3 :=
    (Run.assign hev0).mono (by simp [Expr.size])
  have hn2 : σ2.vars "n" = n := by simp [hσ2, Env.setVar]
  have hev1 : (add (lit 3) (mul (lit 4) (V "n"))).evalB B σ2 = some (3 + 4 * n) := by
    have h := evalB_add (B := B) (σ := σ2)
      (evalB_lit (show (3 : ℕ) < B by omega))
      (evalB_mul (evalB_lit (show (4 : ℕ) < B by omega))
        (evalB_var (by rw [hn2]; omega)) (by rw [hn2]; omega))
      (by rw [hn2]; omega)
    rwa [hn2] at h
  set σ3 := σ2.setVar "L" (3 + 4 * n) with hσ3
  have hrun3 : Run B (set "L" (add (lit 3) (mul (lit 4) (V "n")))) σ2 σ3 6 :=
    (Run.assign hev1).mono (by simp [Expr.size])
  have hU2 : UInv y 2 σ2 := hU1.setV (by decide) (by decide) _
  have hrt2 : σ2.vars "rt" = 2 := by rw [hσ2]; simp only [Env.setVar]; exact hrt1
  have hU3 : UInv y (3 + 4 * n) σ3 := uinv_step hU2 hrt2 (by omega)
  obtain ⟨σ4, hrun4, ⟨hU4, hrt4⟩, hfv4, -, -, -⟩ :=
    (readUpTo_spec (y := y) (3 + 4 * n) (by omega) hy hB).frame σ3 hU3
  -- read how long the target array is
  have hn4 : σ4.vars "n" = n := by
    rw [hfv4 "n" (by simp [readUpTo, Lax888481Proofs.ReadAll.readBody, Com.wvars]), hσ3]
    simp only [Env.setVar]
    exact hn2
  have haT : (σ4.arrs "a").getD (2 + 4 * n) 0 = T := by
    rw [hU4.2.2.2.1 (2 + 4 * n) (by omega), hoff]
  have hevT : (Expr.get "a" (add (lit 2) (mul (lit 4) (V "n")))).evalB B σ4 = some T := by
    refine evalB_getE (evalB_add (evalB_lit (show (2 : ℕ) < B by omega))
      (evalB_mul (evalB_lit (show (4 : ℕ) < B by omega))
        (evalB_var (by rw [hn4]; omega)) (by rw [hn4]; omega)) (by rw [hn4]; omega))
      (by omega) ?_ ?_
    · rw [hn4, hU4.2.2.1]; omega
    · rw [hn4]; exact haT
  set σ5 := σ4.setVar "rv" T with hσ5
  have hrun5 : Run B (set "rv" (.get "a" (add (lit 2) (mul (lit 4) (V "n"))))) σ4 σ5 7 :=
    (Run.assign hevT).mono (by simp [Expr.size])
  have hL5 : σ5.vars "L" = 3 + 4 * n := by
    rw [hσ5]; simp only [Env.setVar]; exact hU4.1
  have hrv5 : σ5.vars "rv" = T := by simp [hσ5, Env.setVar]
  have hevL : (add (add (V "L") (V "rv")) (lit 1)).evalB B σ5 = some (3 + 4 * n + T + 1) := by
    have h := evalB_add (B := B) (σ := σ5)
      (evalB_add (evalB_var (show σ5.vars "L" < B by rw [hL5]; omega))
        (evalB_var (show σ5.vars "rv" < B by rw [hrv5]; omega))
        (by rw [hL5, hrv5]; omega))
      (evalB_lit (show (1 : ℕ) < B by omega)) (by rw [hL5, hrv5]; omega)
    rwa [hL5, hrv5] at h
  set σ6 := σ5.setVar "L" (3 + 4 * n + T + 1) with hσ6
  have hrun6 : Run B (set "L" (add (add (V "L") (V "rv")) (lit 1))) σ5 σ6 6 :=
    (Run.assign hevL).mono (by simp [Expr.size])
  have hU5 : UInv y (3 + 4 * n) σ5 := hU4.setV (by decide) (by decide) _
  have hrt5 : σ5.vars "rt" = 3 + 4 * n := by
    rw [hσ5]; simp only [Env.setVar]; exact hrt4
  have hU6 : UInv y (3 + 4 * n + T + 1) σ6 := uinv_step hU5 hrt5 (by omega)
  obtain ⟨σ7, hrun7, hU7, hrt7⟩ :=
    readUpTo_spec (y := y) (3 + 4 * n + T + 1) (by omega) hy hB σ6 hU6
  have haeq : σ7.arrs "a" = y := by
    refine List.ext_getElem (by rw [hU7.2.2.1]) fun i h1 h2 => ?_
    have := hU7.2.2.2.1 i (by rw [hrt7]; omega)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
      Option.getD_some] at this
  refine ⟨σ7, ?_, haeq, hU7.2.2.2.2.2, ?_, by rw [hU7.1, hlen], by rw [hrt7, hlen]⟩
  · refine (Run.seq hrun0a (Run.seq hrun0b (Run.seq hrun1 (Run.seq hrun2 (Run.seq hrun3
      (Run.seq hrun4 (Run.seq hrun5 (Run.seq hrun6 hrun7)))))))).mono ?_
    omega
  · rw [hU7.2.2.2.2.1, hrt7, ← hlen]
    simp

end Lax888481Proofs.ReadHdr
