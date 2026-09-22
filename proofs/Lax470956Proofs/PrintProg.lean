import Lax470956Proofs.EmitNat
import Lax470956Proofs.ReadAll

/-!
The printer, as a word RAM program.
-/

namespace Lax470956Proofs.PrintProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956Proofs.PrintModel Lax470956Proofs.EmitNat

abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f

/-! ### A block of numbers -/

/-- Write entry `b + j` of the word, and move on. -/
def numBody : Com :=
  .seq (.assign "v" (.get "a" (add (V "b") (V "j")))) (.seq emitNat (bump "j"))

def numLoop : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "J")) numBody)

variable {B : ℕ} {y : List ℕ}

/-- What the printer's loops all know: the word, and that its entries are small. -/
structure Small (B S : ℕ) (y : List ℕ) : Prop where
  entry : ∀ v ∈ y, v + 4 < B ∧ v.size ≤ S
  len : 8 * y.length + 16 < B

lemma Small.getD_lt {S : ℕ} (hs : Small B S y) (n : ℕ) : y.getD n 0 + 4 < B := by
  rcases Nat.lt_or_ge n y.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    exact (hs.entry _ (List.getElem_mem h)).1
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    have := hs.len; simp; omega

lemma Small.getD_size {S : ℕ} (hs : Small B S y) (n : ℕ) : (y.getD n 0).size ≤ S := by
  rcases Nat.lt_or_ge n y.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    exact (hs.entry _ (List.getElem_mem h)).2
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; simp

def NInv (y : List ℕ) (b0 J0 : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = y ∧ σ.vars "b" = b0 ∧ σ.vars "J" = J0 ∧ σ.vars "j" ≤ J0 ∧
    σ.out = out0 ++ (List.range (σ.vars "j")).flatMap fun j => bitsNat (y.getD (b0 + j) 0)

lemma wvars_emitNat : emitNat.wvars = ["s", "u", "u", "s", "i2", "i2", "u", "i2", "u", "i2"] := by
  simp [emitNat, sizeLoop, sizeBody, onesLoop, onesBody, digLoop, digBody, Com.wvars]

lemma warrs_emitNat : emitNat.warrs = [] := by
  simp [emitNat, sizeLoop, sizeBody, onesLoop, onesBody, digLoop, digBody, Com.warrs]

theorem numBody_spec {S : ℕ} (hs : Small B S y) (b0 J0 : ℕ) (out0 : List ℕ)
    (hb : b0 + J0 ≤ y.length) :
    Spec B (fun σ => NInv y b0 J0 out0 σ ∧ σ.vars "j" < J0) numBody
      (fun σ σ' => NInv y b0 J0 out0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) (48 * S + 60) := by
  have hlen := hs.len
  run_vcg [(emitNat_spec (B := B) S).frame]
  all_goals obtain ⟨ha, hbv, hJ, hjle, hout⟩ := ‹NInv y b0 J0 out0 σ›
  all_goals have hjlt := ‹σ.vars "j" < J0›
  all_goals have hidx : b0 + σ.vars "j" < y.length := (by omega)
  all_goals have hmem : y.getD (b0 + σ.vars "j") 0 ∈ y := (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
    exact List.getElem_mem hidx)
  all_goals have hent := hs.entry _ hmem
  all_goals have hav : (σ.arrs "a").getD (σ.vars "b" + σ.vars "j") 0
      = y.getD (b0 + σ.vars "j") 0 := (by rw [ha, hbv])
  · obtain ⟨hout', hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
    have hj' := hfv "j" (by simp [wvars_emitNat])
    have hb' := hfv "b" (by simp [wvars_emitNat])
    have hJ' := hfv "J" (by simp [wvars_emitNat])
    have ha' := hfa "a" (by simp [warrs_emitNat])
    simp only [Env.setVar] at hout'
    simp at hj' hb' hJ' ha'
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [ha'] using ha
    · simpa [hb'] using hbv
    · simpa [hJ'] using hJ
    · simp [hj']; omega
    · simp [hj', hout', hout, List.range_succ, List.flatMap_append, ha, hbv]
    · simp [hj']
  all_goals first
    | omega
    | (rw [ha, hbv]; exact hidx)
    | (rw [hav]; omega)
    | (have hv : ∀ X, (σ.setVar "v" X).vars "v" = X := (by intro X; simp [Env.setVar])
       rw [hv, hav]; exact hent)
    | (obtain ⟨-, hfv, -, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
       have hj' := hfv "j" (by simp [wvars_emitNat])
       simp at hj'
       omega)

theorem numLoop_spec {S : ℕ} (hs : Small B S y) (b0 J0 : ℕ) (out0 : List ℕ)
    (hb : b0 + J0 ≤ y.length) :
    Spec B (fun σ => NInv y b0 J0 out0 (σ.setVar "j" 0)) numLoop
      (fun _ σ' => NInv y b0 J0 out0 σ' ∧ σ'.vars "j" = J0) ((48 * S + 60 + 4) * J0 + 6) :=
  Spec.forRangeZero "j" "J" (NInv y b0 J0 out0) J0 (48 * S + 60) (by have := hs.len; omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (numBody_spec hs b0 J0 out0 hb)

/-! ### One cell of the eligibility matrix -/

open Lax470956.InstanceEncoding

open Classical in
/-- Whether machine `i` has been seen among the first `t` targets, inside the window. -/
noncomputable def seen (y : List ℕ) (lo hi i t : ℕ) : ℕ :=
  if ∃ t' < t, lo ≤ t' ∧ t' < hi ∧ target y t' = i then 1 else 0

lemma seen_zero (lo hi i : ℕ) : seen y lo hi i 0 = 0 := by simp [seen]

lemma seen_succ_hit {lo hi i t : ℕ} (h1 : lo ≤ t) (h2 : t < hi) (h3 : target y t = i) :
    seen y lo hi i (t + 1) = 1 := by
  rw [seen, if_pos ⟨t, by omega, h1, h2, h3⟩]

lemma seen_succ_miss {lo hi i t : ℕ} (h : ¬(lo ≤ t ∧ t < hi ∧ target y t = i)) :
    seen y lo hi i (t + 1) = seen y lo hi i t := by
  unfold seen
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨t', ht', hc⟩
    rcases Nat.lt_or_ge t' t with hlt | hge
    · exact ⟨t', hlt, hc⟩
    · have : t' = t := by omega
      subst this; exact absurd hc h
  · rintro ⟨t', ht', hc⟩; exact ⟨t', by omega, hc⟩

lemma seen_le_one (lo hi i t : ℕ) : seen y lo hi i t ≤ 1 := by
  unfold seen; split_ifs <;> omega

lemma seen_room (j i : ℕ) :
    seen y (offset y j) (offset y (j + 1)) i (room y) = eligBit y j i := by
  unfold seen eligBit
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨t, ht, h1, h2, h3⟩; exact ⟨t, by omega, by omega, h3⟩
  · rintro ⟨t, h1, h2, h3⟩; exact ⟨t, by omega, by omega, by omega, h3⟩

/-- What the matrix loops all know. -/
def PCtx (y : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ σ.vars "J" = jobCount y ∧
    σ.vars "M" = machineCount y ∧ σ.vars "T0" = 3 + 4 * jobCount y ∧
    σ.vars "O0" = 2 + 3 * jobCount y ∧ σ.vars "R" = room y

def pctxVars : List String := ["L", "J", "M", "T0", "O0", "R"]

theorem PCtx.setVar {σ : Env} (h : PCtx y σ) (x : String) (v : ℕ) (hx : x ∉ pctxVars) :
    PCtx y (σ.setVar x v) := by
  simp only [pctxVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  simpa [PCtx, Env.setVar, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5,
    Ne.symm h6] using h

lemma PCtx.of_write {σ : Env} (h : PCtx y σ) (l : List ℕ) :
    PCtx y { vars := σ.vars, arrs := σ.arrs, inp := σ.inp, out := l } := by
  simpa [PCtx] using h

def scanBody : Com :=
  .seq (.ite (.lt (V "t") (V "lo")) .skip
      (.ite (.lt (V "t") (V "hi"))
        (.ite (.eq (.get "a" (add (V "T0") (V "t"))) (V "i")) (.assign "f" (.lit 1)) .skip)
        .skip))
    (bump "t")

def scanLoop : Com := .seq (.assign "t" (.lit 0)) (.while (.lt (V "t") (V "R")) scanBody)

def SInv (y : List ℕ) (lo hi i : ℕ) (σ : Env) : Prop :=
  PCtx y σ ∧ σ.vars "lo" = lo ∧ σ.vars "hi" = hi ∧ σ.vars "i" = i ∧ σ.vars "t" ≤ room y ∧
    σ.vars "f" = seen y lo hi i (σ.vars "t")

theorem scanBody_spec {S : ℕ} (hs : Small B S y) (hg : Guard y) (lo hi i : ℕ)
    (hloB : lo < B) (hhiB : hi < B) (hiB : i < B) :
    Spec B (fun σ => SInv y lo hi i σ ∧ σ.vars "t" < room y) scanBody
      (fun σ σ' => SInv y lo hi i σ' ∧ σ'.vars "t" = σ.vars "t" + 1) 40 := by
  have hlen := hs.len
  have hroom : room y = y.length - (3 + 4 * jobCount y) := rfl
  have hg1 := hg.1
  run_vcg
  all_goals obtain ⟨hctx, hlo, hhi, hi', ht, hf⟩ := ‹SInv y lo hi i σ›
  all_goals have hctx0 := hctx
  all_goals obtain ⟨ha, hL, hJ, hM, hT0, hO0, hR⟩ := hctx
  all_goals have htlt := ‹σ.vars "t" < room y›
  all_goals have htg : (σ.arrs "a").getD (σ.vars "T0" + σ.vars "t") 0 = target y (σ.vars "t") :=
    (by rw [ha, hT0]; rfl)
  all_goals have hgl := hs.getD_lt (3 + 4 * jobCount y + σ.vars "t")
  · refine ⟨⟨hctx0.setVar _ _ (by decide), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [Env.setVar, hlo, hhi, hi', hf]
    · omega
    · rw [seen_succ_miss]; omega
  · refine ⟨⟨(hctx0.setVar _ _ (by decide)).setVar _ _ (by decide), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [Env.setVar, hlo, hhi, hi']
    · omega
    · rw [seen_succ_hit (by omega) (by omega) (by rw [← htg, ← hi']; assumption)]
  · refine ⟨⟨hctx0.setVar _ _ (by decide), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [Env.setVar, hlo, hhi, hi', hf]
    · omega
    · rw [seen_succ_miss]; rintro ⟨-, -, h3⟩; rw [← htg, ← hi'] at h3; contradiction
  · refine ⟨⟨hctx0.setVar _ _ (by decide), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [Env.setVar, hlo, hhi, hi', hf]
    · omega
    · rw [seen_succ_miss]; omega
  all_goals first
    | omega
    | (rw [ha]; omega)
    | (rw [htg]; unfold target; omega)

theorem scanLoop_ghost {S : ℕ} (hs : Small B S y) (hg : Guard y) (lo hi i : ℕ)
    (hloB : lo < B) (hhiB : hi < B) (hiB : i < B) :
    Spec B (fun σ => SInv y lo hi i (σ.setVar "t" 0)) scanLoop
      (fun _ σ' => SInv y lo hi i σ' ∧ σ'.vars "t" = room y) ((40 + 4) * room y + 6) :=
  Spec.forRangeZero "t" "R" (SInv y lo hi i) (room y) 40
    (by have := hs.len; unfold room; omega)
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.1.2.2.2.2.2.2) (scanBody_spec hs hg lo hi i hloB hhiB hiB)

/-- **One cell.** Nothing is said of what the loop leaves alone; read it off `Spec.frame`. -/
theorem scanLoop_spec {S : ℕ} (hs : Small B S y) (hg : Guard y) :
    Spec B (fun σ => PCtx y σ ∧ σ.vars "f" = 0 ∧ σ.vars "lo" < B ∧ σ.vars "hi" < B ∧
        σ.vars "i" < B) scanLoop
      (fun σ σ' => PCtx y σ' ∧
        σ'.vars "f" = seen y (σ.vars "lo") (σ.vars "hi") (σ.vars "i") (room y))
      (44 * room y + 6) := by
  intro σ ⟨hctx, hf, h1, h2, h3⟩
  obtain ⟨σ', hrun, hI, ht⟩ := scanLoop_ghost hs hg _ _ _ h1 h2 h3 σ
    ⟨hctx.setVar _ _ (by decide), by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar, hf, seen_zero]⟩
  exact ⟨σ', hrun, hI.1, by rw [hI.2.2.2.2.2, ht]⟩

lemma wvars_scanLoop : scanLoop.wvars = ["t", "f", "t"] := by
  simp [scanLoop, scanBody, Com.wvars]

lemma noWrite_scanLoop : scanLoop.NoWrite := by
  simp [scanLoop, scanBody, Com.NoWrite]

def cell : Com :=
  .seq (.assign "f" (.lit 0)) (.seq scanLoop (.seq (.write (V "f")) (bump "i")))

def CInv (y : List ℕ) (j0 : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  PCtx y σ ∧ σ.vars "j" = j0 ∧ σ.vars "lo" = offset y j0 ∧ σ.vars "hi" = offset y (j0 + 1) ∧
    σ.vars "i" ≤ machineCount y ∧
    σ.out = out0 ++ (List.range (σ.vars "i")).map (eligBit y j0)

theorem cell_spec {S : ℕ} (hs : Small B S y) (hg : Guard y) (j0 : ℕ) (out0 : List ℕ) (K : ℕ)
    (hK : 44 * room y + 6 = K) :
    Spec B (fun σ => CInv y j0 out0 σ ∧ σ.vars "i" < machineCount y) cell
      (fun σ σ' => CInv y j0 out0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) (K + 30) := by
  have hlen := hs.len
  have hg2 := hg.2
  have hnw := noWrite_scanLoop
  have hsc : Spec B _ scanLoop _ K := hK ▸ (scanLoop_spec (B := B) hs hg)
  run_vcg [hsc.frame]
  all_goals obtain ⟨hctx, hj, hlo, hhi, hi', hout⟩ := ‹CInv y j0 out0 σ›
  all_goals have hilt := ‹σ.vars "i" < machineCount y›
  all_goals have h1 := hs.getD_lt (2 + 3 * jobCount y + j0)
  all_goals have h2 := hs.getD_lt (2 + 3 * jobCount y + (j0 + 1))
  all_goals have hsl := seen_le_one (y := y) (offset y j0) (offset y (j0 + 1)) (σ.vars "i") (room y)
  all_goals have hM : machineCount y + 4 < B := (by omega)
  all_goals try
    (obtain ⟨⟨hctx', hf'⟩, hfv, hfa, -, hfo⟩ := ‹(PCtx y _ ∧ _) ∧ (∀ y ∉ scanLoop.wvars, _) ∧ _›
     have hi2 := hfv "i" (by simp [wvars_scanLoop])
     have hj2 := hfv "j" (by simp [wvars_scanLoop])
     have hlo2 := hfv "lo" (by simp [wvars_scanLoop])
     have hhi2 := hfv "hi" (by simp [wvars_scanLoop])
     have hout2 := hfo hnw
     simp only [Env.setVar] at hi2 hj2 hlo2 hhi2 hout2 hf'
     simp at hi2 hj2 hlo2 hhi2 hf'
     rw [hlo, hhi, seen_room] at hf')
  · refine ⟨⟨(hctx'.of_write _).setVar _ _ (by decide), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [Env.setVar, hi2, hj2, hlo2, hhi2, hj, hlo, hhi, hout2, hout, hf', List.range_succ]
    omega
  · refine ⟨hctx.setVar _ _ (by decide), ?_⟩
    simp [Env.setVar]
    unfold offset at hlo hhi
    omega
  all_goals first
    | (rw [hf', ← seen_room]; omega)
    | (simp [hi2]; omega)

/-! ### A row, and the matrix -/

def iLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "M")) cell)

theorem iLoop_ghost {S : ℕ} (hs : Small B S y) (hg : Guard y) (j0 : ℕ) (out0 : List ℕ) (K : ℕ)
    (hK : 44 * room y + 6 = K) :
    Spec B (fun σ => CInv y j0 out0 (σ.setVar "i" 0)) iLoop
      (fun _ σ' => CInv y j0 out0 σ' ∧ σ'.vars "i" = machineCount y)
      ((K + 30 + 4) * machineCount y + 6) :=
  Spec.forRangeZero "i" "M" (CInv y j0 out0) (machineCount y) (K + 30)
    (by have := hs.len; have := hg.2; omega)
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.1.2.2.2.1) (cell_spec hs hg j0 out0 K hK)

theorem iLoop_spec {S : ℕ} (hs : Small B S y) (hg : Guard y) (K : ℕ)
    (hK : 44 * room y + 6 = K) :
    Spec B (fun σ => PCtx y σ ∧ σ.vars "lo" = offset y (σ.vars "j") ∧
        σ.vars "hi" = offset y (σ.vars "j" + 1)) iLoop
      (fun σ σ' => PCtx y σ' ∧
        σ'.out = σ.out ++ (List.range (machineCount y)).map (eligBit y (σ.vars "j")))
      ((K + 30 + 4) * machineCount y + 6) := by
  intro σ ⟨hctx, h1, h2⟩
  obtain ⟨σ', hrun, hI, hi⟩ := iLoop_ghost hs hg (σ.vars "j") σ.out K hK σ
    ⟨hctx.setVar _ _ (by decide), by simp [Env.setVar], by simp [Env.setVar, h1],
      by simp [Env.setVar, h2], by simp [Env.setVar], by simp [Env.setVar]⟩
  exact ⟨σ', hrun, hI.1, by rw [hI.2.2.2.2.2, hi]⟩

lemma wvars_iLoop : iLoop.wvars = ["i", "f", "t", "f", "t", "i"] := by
  simp [iLoop, cell, scanLoop, scanBody, Com.wvars]

def row : Com :=
  .seq (.assign "lo" (.get "a" (add (V "O0") (V "j"))))
    (.seq (.assign "hi" (.get "a" (add (add (V "O0") (V "j")) (.lit 1))))
      (.seq iLoop (bump "j")))

def mLoop : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "J")) row)

def MInv (y : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  PCtx y σ ∧ σ.vars "j" ≤ jobCount y ∧
    σ.out = out0 ++ (List.range (σ.vars "j")).flatMap
      fun j => (List.range (machineCount y)).map (eligBit y j)

theorem row_spec {S : ℕ} (hs : Small B S y) (hg : Guard y) (out0 : List ℕ) (K K2 : ℕ)
    (hK : 44 * room y + 6 = K) (hK2 : (K + 30 + 4) * machineCount y + 6 = K2) :
    Spec B (fun σ => MInv y out0 σ ∧ σ.vars "j" < jobCount y) row
      (fun σ σ' => MInv y out0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) (K2 + 30) := by
  have hlen := hs.len
  have hg1 := hg.1
  have hsc : Spec B _ iLoop _ K2 := hK2 ▸ (iLoop_spec (B := B) hs hg K hK)
  run_vcg [hsc.frame]
  all_goals obtain ⟨hctx, hjle, hout⟩ := ‹MInv y out0 σ›
  all_goals have hctx0 := hctx
  all_goals obtain ⟨ha, hL, hJ, hM, hT0, hO0, hR⟩ := hctx
  all_goals have hjlt := ‹σ.vars "j" < jobCount y›
  all_goals have h1 := hs.getD_lt (2 + 3 * jobCount y + σ.vars "j")
  all_goals have h2 := hs.getD_lt (2 + 3 * jobCount y + σ.vars "j" + 1)
  all_goals try
    (obtain ⟨⟨hctx', hout'⟩, hfv, -, -, -⟩ := ‹(PCtx y _ ∧ _) ∧ (∀ y ∉ iLoop.wvars, _) ∧ _›
     have hj2 := hfv "j" (by simp [wvars_iLoop])
     simp [Env.setVar] at hj2 hout')
  · refine ⟨⟨hctx'.setVar _ _ (by decide), ?_, ?_⟩, ?_⟩ <;>
      simp [Env.setVar, hj2, hout', hout, List.range_succ, List.flatMap_append]
    omega
  all_goals try simp only [Env.setVar, if_neg (by decide : ¬ ("O0" = "lo")), if_neg (by decide : ¬ ("j" = "lo"))]
  all_goals first
    | omega
    | (rw [ha]; omega)
    | (rw [ha, hO0]; omega)
    | (refine ⟨(hctx0.setVar "lo" _ (by decide)).setVar "hi" _ (by decide), ?_, ?_⟩ <;>
        simp [Env.setVar, offset, ha, hO0, Nat.add_assoc])
    | (simp [hj2]; omega)

theorem mLoop_ghost {S : ℕ} (hs : Small B S y) (hg : Guard y) (out0 : List ℕ) (K K2 : ℕ)
    (hK : 44 * room y + 6 = K) (hK2 : (K + 30 + 4) * machineCount y + 6 = K2) :
    Spec B (fun σ => MInv y out0 (σ.setVar "j" 0)) mLoop
      (fun _ σ' => MInv y out0 σ' ∧ σ'.vars "j" = jobCount y)
      ((K2 + 30 + 4) * jobCount y + 6) :=
  Spec.forRangeZero "j" "J" (MInv y out0) (jobCount y) (K2 + 30)
    (by have := hs.len; have := hg.1; omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.2.1) (row_spec hs hg out0 K K2 hK hK2)

/-- **The matrix.** -/
theorem mLoop_spec {S : ℕ} (hs : Small B S y) (hg : Guard y) (K K2 : ℕ)
    (hK : 44 * room y + 6 = K) (hK2 : (K + 30 + 4) * machineCount y + 6 = K2) :
    Spec B (fun σ => PCtx y σ) mLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range (jobCount y)).flatMap
        fun j => (List.range (machineCount y)).map (eligBit y j))
      ((K2 + 30 + 4) * jobCount y + 6) := by
  intro σ hctx
  obtain ⟨σ', hrun, hI, hj⟩ := mLoop_ghost hs hg σ.out K K2 hK hK2 σ
    ⟨hctx.setVar _ _ (by decide), by simp [Env.setVar], by simp [Env.setVar]⟩
  exact ⟨σ', hrun, by show σ'.out = _; rw [hI.2.2, hj]⟩

/-- **A block of numbers.** -/
theorem numLoop_spec' {S : ℕ} (hs : Small B S y) :
    Spec B (fun σ => σ.arrs "a" = y ∧ σ.vars "J" = jobCount y ∧
        σ.vars "b" + jobCount y ≤ y.length) numLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range (jobCount y)).flatMap
        fun j => bitsNat (y.getD (σ.vars "b" + j) 0))
      ((48 * S + 60 + 4) * jobCount y + 6) := by
  intro σ ⟨ha, hJ, hb⟩
  obtain ⟨σ', hrun, hI, hj⟩ := numLoop_spec hs (σ.vars "b") (jobCount y) σ.out hb σ
    ⟨by simpa [Env.setVar] using ha, by simp [Env.setVar], by simpa [Env.setVar] using hJ,
      by simp [Env.setVar], by simp [Env.setVar]⟩
  exact ⟨σ', hrun, by show σ'.out = _; rw [hI.2.2.2.2, hj]⟩

lemma wvars_numLoop :
    numLoop.wvars = ["j", "v", "s", "u", "u", "s", "i2", "i2", "u", "i2", "u", "i2", "j"] := by
  simp [numLoop, numBody, Com.wvars, wvars_emitNat]

lemma warrs_numLoop : numLoop.warrs = [] := by
  simp [numLoop, numBody, Com.warrs, warrs_emitNat]

/-- The context survives whatever leaves its scalars and the array alone. -/
theorem PCtx.congr {σ σ' : Env} (h : PCtx y σ) (hv : ∀ x ∈ pctxVars, σ'.vars x = σ.vars x)
    (ha : σ'.arrs "a" = σ.arrs "a") : PCtx y σ' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨ha ▸ h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv "L" (by decide)]; exact h1
  · rw [hv "J" (by decide)]; exact h2
  · rw [hv "M" (by decide)]; exact h3
  · rw [hv "T0" (by decide)]; exact h4
  · rw [hv "O0" (by decide)]; exact h5
  · rw [hv "R" (by decide)]; exact h6

end Lax470956Proofs.PrintProg
