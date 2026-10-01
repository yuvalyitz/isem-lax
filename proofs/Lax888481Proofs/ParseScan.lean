import Lax888481Proofs.ParseSem
import Lax888481Proofs.ReadAll

/-!
The parser's scan, as an IMP+ loop: one bit a step, the state of `ParseModel` in five
scalars and two arrays.
-/

namespace Lax888481Proofs.ParseScan

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax434930.PolynomialTime
open Lax888481Proofs.ParseModel Lax888481Proofs.ParseSem Lax888481Proofs.Theorem2Assembly

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))
abbrev set (s : String) (n : ℕ) : Com := .assign s (.lit n)

/-- The literals read so far. -/
def flat (s : St) : List Literal := litsOf s.done ++ s.cur

lemma litsOf_append (d : List Clause) (c : Clause) : litsOf (d ++ [c]) = litsOf d ++ c := by
  simp [litsOf]

/-- The sizes of the state are bounded by the number of bits read. -/
def size (s : St) : ℕ := max (max s.n (flat s).length) (max s.done.length s.cur.length)

lemma size_step (s : St) (b : Bool) : size (step s b) ≤ size s + 1 := by
  obtain ⟨ph, n, d, c⟩ := s
  have hl : (litsOf (d ++ [c])).length = (litsOf d).length + c.length := by
    rw [litsOf_append, List.length_append]
  match ph with
  | 0 => cases b <;> simp [step, size, flat]
  | 1 =>
      by_cases h : c.length < 3 <;> cases b <;>
        simp [step, size, flat, h, litsOf_append] <;> omega
  | 2 => cases b <;> simp [step, size, flat] <;> omega
  | 3 => simp [step, size, flat]; omega
  | k + 4 => simp [step, size, flat]

lemma size_run (w : Word) : size (run init w) ≤ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [size, init, flat, litsOf]
  | append_singleton u b ih =>
      rw [run_append]; simp only [run_cons, run_nil, List.length_append, List.length_singleton]
      exact le_trans (size_step _ _) (by omega)

/-- The environment reflects a state of the scan. -/
structure Refl (s : St) (σ : Env) : Prop where
  ph : σ.vars "ph" = s.ph
  n : σ.vars "n" = s.n
  h : σ.vars "h" = s.cur.length
  C : σ.vars "C" = s.done.length
  k : σ.vars "k" = (flat s).length
  vr : ∀ i < (flat s).length, (σ.arrs "vr").getD i 0 = ((flat s).getD i dflt).index
  sg : ∀ i < (flat s).length,
    (σ.arrs "sg").getD i 0 = if ((flat s).getD i dflt).positive then 1 else 0

def phase3 : Com :=
  .seq (.store "vr" (V "k") (V "n"))
    (.seq (.ite (.eq (V "c") (.lit 0)) (.store "sg" (V "k") (.lit 0)) (.store "sg" (V "k") (.lit 1)))
      (.seq (bump "k") (.seq (bump "h") (set "ph" 1))))

def phase1 : Com :=
  .ite (.lt (V "h") (.lit 3))
    (.ite (.eq (V "c") (.lit 0)) (set "ph" 5) (.seq (set "ph" 2) (set "n" 0)))
    (.ite (.eq (V "c") (.lit 0)) (.seq (set "ph" 0) (.seq (bump "C") (set "h" 0))) (set "ph" 5))

def dispatch : Com :=
  .ite (.eq (V "ph") (.lit 0)) (.ite (.eq (V "c") (.lit 0)) (set "ph" 4) (set "ph" 1))
    (.ite (.eq (V "ph") (.lit 1)) phase1
      (.ite (.eq (V "ph") (.lit 2)) (.ite (.eq (V "c") (.lit 0)) (set "ph" 3) (bump "n"))
        (.ite (.eq (V "ph") (.lit 3)) phase3 (set "ph" 5))))

def scanBody : Com := .seq (.assign "c" (.get "a" (V "p"))) (.seq dispatch (bump "p"))

def scanLoop : Com := .seq (set "p" 0) (.while (.lt (V "p") (V "L")) scanBody)

variable {B : ℕ}

lemma ph_step_le (s : St) (b : Bool) (h : s.ph ≤ 5) : (step s b).ph ≤ 5 := by
  obtain ⟨ph, n, d, c⟩ := s
  simp only at h
  have : ph = 0 ∨ ph = 1 ∨ ph = 2 ∨ ph = 3 ∨ ph = 4 ∨ ph = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> simp [step] <;>
    split_ifs <;> simp

lemma ph_run_le (w : Word) : (run init w).ph ≤ 5 := by
  induction w using List.reverseRecOn with
  | nil => simp [init]
  | append_singleton u b ih => rw [run_append]; exact ph_step_le _ _ ih

/-- Reflection survives a step that leaves the literals and the arrays alone. -/
lemma Refl.scalars {s s' : St} {σ σ' : Env} (h : Refl s σ) (hf : flat s' = flat s)
    (hvr : σ'.arrs "vr" = σ.arrs "vr") (hsg : σ'.arrs "sg" = σ.arrs "sg")
    (hk : σ'.vars "k" = σ.vars "k") (hph : σ'.vars "ph" = s'.ph) (hn : σ'.vars "n" = s'.n)
    (hh : σ'.vars "h" = s'.cur.length) (hC : σ'.vars "C" = s'.done.length) : Refl s' σ' :=
  ⟨hph, hn, hh, hC, by rw [hk, hf, h.k], by rw [hf, hvr]; exact h.vr, by rw [hf, hsg]; exact h.sg⟩

def DPre (B : ℕ) (s : St) (b : Bool) (M : ℕ) (σ : Env) : Prop :=
  Refl s σ ∧ (σ.vars "c" = 0 ↔ b = false) ∧ σ.vars "c" < B ∧
    (σ.arrs "vr").length = M ∧ (σ.arrs "sg").length = M

def DPost (s : St) (b : Bool) (M : ℕ) (σ' : Env) : Prop :=
  Refl (step s b) σ' ∧ (σ'.arrs "vr").length = M ∧ (σ'.arrs "sg").length = M

theorem phase1_spec (s : St) (b : Bool) (M : ℕ) (hM : M + 8 < B) (hs : size s < M) :
    Spec B (fun σ => DPre B s b M σ ∧ σ.vars "ph" = 1) phase1
      (fun _ σ' => DPost s b M σ') 20 := by
  obtain ⟨ph, n, d, c⟩ := s
  simp only [size, flat] at hs
  run_vcg
  all_goals obtain ⟨hR, hiff, hcB, hl1, hl2⟩ := ‹DPre B _ b M σ›
  all_goals have hp1 : ph = 1 := (by have := hR.ph; simp only at this; omega)
  all_goals subst hp1
  all_goals have hh := hR.h
  all_goals have hC := hR.C
  all_goals simp only at hh hC
  · have hb : b = false := hiff.mp ‹_›
    subst hb
    have hlt : c.length < 3 := by omega
    exact ⟨hR.scalars (by simp [step, hlt, flat]) rfl rfl rfl (by simp [step, hlt, Env.setVar])
      (by simpa [step, hlt, Env.setVar] using hR.n) (by simpa [step, hlt, Env.setVar] using hh)
      (by simpa [step, hlt, Env.setVar] using hC), hl1, hl2⟩
  · have hb : b = true := by cases b <;> simp_all
    subst hb
    have hlt : c.length < 3 := by omega
    exact ⟨hR.scalars (by simp [step, hlt, flat]) rfl rfl rfl (by simp [step, hlt, Env.setVar])
      (by simp [step, hlt, Env.setVar]) (by simpa [step, hlt, Env.setVar] using hh)
      (by simpa [step, hlt, Env.setVar] using hC), hl1, hl2⟩
  · have hb : b = false := hiff.mp ‹_›
    subst hb
    have hlt : ¬ c.length < 3 := by omega
    exact ⟨hR.scalars (by simp [step, hlt, flat, litsOf_append]) rfl rfl rfl
      (by simp [step, hlt, Env.setVar])
      (by simpa [step, hlt, Env.setVar] using hR.n) (by simp [step, hlt, Env.setVar])
      (by simp [step, hlt, Env.setVar, hC]), hl1, hl2⟩
  · have hb : b = true := by cases b <;> simp_all
    subst hb
    have hlt : ¬ c.length < 3 := by omega
    exact ⟨hR.scalars (by simp [step, hlt, flat]) rfl rfl rfl (by simp [step, hlt, Env.setVar])
      (by simpa [step, hlt, Env.setVar] using hR.n) (by simpa [step, hlt, Env.setVar] using hh)
      (by simpa [step, hlt, Env.setVar] using hC), hl1, hl2⟩
  all_goals first
    | omega
    | (simp only [Env.setVar]; simp; omega)

lemma getD_set_snoc {α : Type} (arr : List ℕ) (L : List α) (f : α → ℕ) (x d : α)
    (hlen : L.length < arr.length) (h : ∀ i < L.length, arr.getD i 0 = f (L.getD i d)) :
    ∀ i < (L ++ [x]).length, (arr.set L.length (f x)).getD i 0 = f ((L ++ [x]).getD i d) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i L.length with hlt | hge
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD,
      h i hlt, List.getD_append _ _ _ _ hlt]
  · have : i = L.length := by omega
    subst this
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlen, List.getD_append_right _ _ _ _ (le_refl _)]
    simp

theorem phase3_spec (s : St) (b : Bool) (M : ℕ) (hM : M + 8 < B) (hs : size s < M) :
    Spec B (fun σ => DPre B s b M σ ∧ σ.vars "ph" = 3) phase3
      (fun _ σ' => DPost s b M σ') 30 := by
  obtain ⟨ph, n, d, c⟩ := s
  simp only [size, flat] at hs
  run_vcg
  all_goals obtain ⟨hR, hiff, hcB, hl1, hl2⟩ := ‹DPre B _ b M σ›
  all_goals have hp1 : ph = 3 := (by have := hR.ph; simp only at this; omega)
  all_goals subst hp1
  all_goals obtain ⟨-, hn, hh, hC, hk, hvr, hsg⟩ := hR
  all_goals simp only [flat] at hn hh hC hk hvr hsg
  all_goals have hkM : (litsOf d ++ c).length < M := (by omega)
  all_goals try simp only [Env.setArr, Env.setVar]
  all_goals try simp only [if_neg (by decide : ¬ ("k" = "h")), if_pos, if_true]
  · have hb : b = false := hiff.mp ‹_›
    subst hb
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [step]
    · simpa [step] using hn
    · simp [step, hh]
    · simpa [step] using hC
    · simp [step, flat, hk]; omega
    · have := getD_set_snoc (σ.arrs "vr") (litsOf d ++ c) Literal.index ⟨n, false⟩ dflt
        (by omega) hvr
      simpa [step, flat, hk, hn] using this
    · have := getD_set_snoc (σ.arrs "sg") (litsOf d ++ c)
        (fun l => if l.positive then 1 else 0) ⟨n, false⟩ dflt (by omega) hsg
      simpa [step, flat, hk] using this
    · simp [hl1]
    · simp [hl2]
  · have hb : b = true := by cases b <;> simp_all
    subst hb
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [step]
    · simpa [step] using hn
    · simp [step, hh]
    · simpa [step] using hC
    · simp [step, flat, hk]; omega
    · have := getD_set_snoc (σ.arrs "vr") (litsOf d ++ c) Literal.index ⟨n, true⟩ dflt
        (by omega) hvr
      simpa [step, flat, hk, hn] using this
    · have := getD_set_snoc (σ.arrs "sg") (litsOf d ++ c)
        (fun l => if l.positive then 1 else 0) ⟨n, true⟩ dflt (by omega) hsg
      simpa [step, flat, hk] using this
    · simp [hl1]
    · simp [hl2]
  all_goals first
    | omega
    | (simp; omega)
    | (rw [if_neg (by decide)]; omega)

theorem dispatch_spec (s : St) (b : Bool) (M : ℕ) (hM : M + 8 < B) (hs : size s < M)
    (hph5 : s.ph ≤ 5) :
    Spec B (fun σ => DPre B s b M σ) dispatch (fun _ σ' => DPost s b M σ') 60 := by
  have h1 := phase1_spec (B := B) s b M hM hs
  have h3 := phase3_spec (B := B) s b M hM hs
  obtain ⟨ph, n, d, c⟩ := s
  simp only at hph5
  simp only [size, flat] at hs
  run_vcg [h1, h3]
  all_goals have hD := ‹DPre B _ b M σ›
  all_goals obtain ⟨hR, hiff, hcB, hl1, hl2⟩ := hD
  all_goals have hphv := hR.ph
  all_goals have hh := hR.h
  all_goals have hC := hR.C
  all_goals have hn := hR.n
  all_goals simp only at hphv hh hC hn
  all_goals try omega
  all_goals try (exact ⟨‹DPre B _ b M σ›, ‹_›⟩)
  all_goals try (exact ‹DPost _ b M _›)
  · have hp : ph = 0 := by omega
    have hb : b = false := hiff.mp ‹_›
    subst hp hb
    exact ⟨hR.scalars (by simp [step, flat]) rfl rfl rfl (by simp [step, Env.setVar])
      (by simpa [step, Env.setVar] using hn) (by simpa [step, Env.setVar] using hh)
      (by simpa [step, Env.setVar] using hC), hl1, hl2⟩
  · have hp : ph = 0 := by omega
    have hb : b = true := by cases b <;> simp_all
    subst hp hb
    exact ⟨hR.scalars (by simp [step, flat]) rfl rfl rfl (by simp [step, Env.setVar])
      (by simpa [step, Env.setVar] using hn) (by simpa [step, Env.setVar] using hh)
      (by simpa [step, Env.setVar] using hC), hl1, hl2⟩
  · have hp : ph = 2 := by omega
    have hb : b = false := hiff.mp ‹_›
    subst hp hb
    exact ⟨hR.scalars (by simp [step, flat]) rfl rfl rfl (by simp [step, Env.setVar])
      (by simpa [step, Env.setVar] using hn) (by simpa [step, Env.setVar] using hh)
      (by simpa [step, Env.setVar] using hC), hl1, hl2⟩
  · have hp : ph = 2 := by omega
    have hb : b = true := by cases b <;> simp_all
    subst hp hb
    exact ⟨hR.scalars (by simp [step, flat]) rfl rfl rfl (by simpa [step, Env.setVar] using hphv)
      (by simp [step, Env.setVar, hn]) (by simpa [step, Env.setVar] using hh)
      (by simpa [step, Env.setVar] using hC), hl1, hl2⟩
  · have hp : ph = 4 ∨ ph = 5 := by omega
    rcases hp with rfl | rfl <;>
    exact ⟨hR.scalars (by simp [step, flat]) rfl rfl rfl (by simp [step, Env.setVar])
      (by simpa [step, Env.setVar] using hn) (by simpa [step, Env.setVar] using hh)
      (by simpa [step, Env.setVar] using hC), hl1, hl2⟩

/-! ### The Loop -/

variable {y : List ℕ}

/-- The state of the scan after `p` entries of the word. -/
def stAt (y : List ℕ) (p : ℕ) : St := run init (bitsOf (y.take p))

lemma stAt_succ {p : ℕ} (hp : p < y.length) :
    stAt y (p + 1) = step (stAt y p) (decide (y.getD p 0 ≠ 0)) := by
  unfold stAt bitsOf
  rw [List.take_succ, List.getElem?_eq_getElem hp, Option.toList_some, List.map_append,
    run_append, List.getD_eq_getElem _ _ hp]
  rfl

lemma size_stAt (p : ℕ) : size (stAt y p) ≤ p := by
  refine le_trans (size_run _) ?_
  simp [bitsOf, List.length_take]

def SInv (y : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ σ.vars "p" ≤ y.length ∧
    (σ.arrs "vr").length = y.length + 1 ∧ (σ.arrs "sg").length = y.length + 1 ∧
    Refl (stAt y (σ.vars "p")) σ

lemma wvars_dispatch : dispatch.wvars = ["ph", "ph", "ph", "ph", "n", "ph", "C", "h", "ph",
    "ph", "n", "k", "h", "ph", "ph"] := by
  simp [dispatch, phase1, phase3, Com.wvars]

lemma warrs_dispatch : dispatch.warrs = ["vr", "sg", "sg"] := by
  simp [dispatch, phase1, phase3, Com.warrs]

theorem scanBody_ghost (hy : ∀ v ∈ y, v < B) (hB : y.length + 9 < B) (p0 : ℕ)
    (hp0 : p0 < y.length) :
    Spec B (fun σ => SInv y σ ∧ σ.vars "p" = p0) scanBody
      (fun _ σ' => SInv y σ' ∧ σ'.vars "p" = p0 + 1) 70 := by
  have hd := (dispatch_spec (B := B) (stAt y p0) (decide (y.getD p0 0 ≠ 0)) (y.length + 1)
    (by omega) (by have := size_stAt (y := y) p0; omega) (ph_run_le _)).frame
  run_vcg [hd]
  all_goals obtain ⟨ha, hL, hple, hl1, hl2, hR⟩ := ‹SInv y σ›
  all_goals have hp := ‹σ.vars "p" = p0›
  all_goals rw [hp] at hR
  all_goals have hyp : y.getD p0 0 < B := (by
    rw [List.getD_eq_getElem _ _ hp0]; exact hy _ (List.getElem_mem hp0))
  · obtain ⟨⟨hR', hl1', hl2'⟩, hfv, hfa, -, -⟩ := ‹DPost _ _ _ _ ∧ _›
    have hpw := hfv "p" (by simp [wvars_dispatch])
    have hLw := hfv "L" (by simp [wvars_dispatch])
    have haw := hfa "a" (by simp [warrs_dispatch])
    simp only [Env.setVar] at hpw hLw haw
    simp at hpw hLw
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [Env.setVar, haw] using ha
    · simpa [Env.setVar, hLw] using hL
    · simp [Env.setVar, hpw, hp]; omega
    · simpa [Env.setVar] using hl1'
    · simpa [Env.setVar] using hl2'
    · have he : ∀ τ : Env, (τ.setVar "p" (τ.vars "p" + 1)).vars "p" = τ.vars "p" + 1 := by
        intro τ; simp [Env.setVar]
      rw [he, hpw, hp, stAt_succ hp0]
      exact hR'.scalars rfl rfl rfl (by simp [Env.setVar]) (by simpa [Env.setVar] using hR'.ph)
        (by simpa [Env.setVar] using hR'.n) (by simpa [Env.setVar] using hR'.h)
        (by simpa [Env.setVar] using hR'.C)
    · simp [Env.setVar, hpw, hp]
  all_goals first
    | (rw [ha, hp]; exact hp0)
    | (rw [ha, hp]; exact hyp)
    | (refine ⟨hR.scalars rfl rfl rfl (by simp [Env.setVar]) (by simpa [Env.setVar] using hR.ph)
        (by simpa [Env.setVar] using hR.n) (by simpa [Env.setVar] using hR.h)
        (by simpa [Env.setVar] using hR.C), ?_, ?_, by simpa [Env.setVar] using hl1,
        by simpa [Env.setVar] using hl2⟩
       · simp only [Env.setVar, if_pos]; rw [ha, hp]; simp
       · simp only [Env.setVar, if_pos]; rw [ha, hp]; simpa using hyp)
    | (obtain ⟨-, hfv, -, -, -⟩ := ‹DPost _ _ _ _ ∧ _›
       have hpw := hfv "p" (by simp [wvars_dispatch])
       simp only [Env.setVar] at hpw
       simp at hpw
       omega)

theorem scanBody_spec (hy : ∀ v ∈ y, v < B) (hB : y.length + 9 < B) :
    Spec B (fun σ => SInv y σ ∧ σ.vars "p" < y.length) scanBody
      (fun σ σ' => SInv y σ' ∧ σ'.vars "p" = σ.vars "p" + 1) 70 :=
  fun σ h => scanBody_ghost hy hB (σ.vars "p") h.2 σ ⟨h.1, rfl⟩

theorem scanLoop_spec (hy : ∀ v ∈ y, v < B) (hB : y.length + 9 < B) :
    Spec B (fun σ => SInv y (σ.setVar "p" 0)) scanLoop
      (fun _ σ' => SInv y σ' ∧ σ'.vars "p" = y.length) ((70 + 4) * y.length + 6) :=
  Spec.forRangeZero "p" "L" (SInv y) y.length 70 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (scanBody_spec hy hB)

end Lax888481Proofs.ParseScan
