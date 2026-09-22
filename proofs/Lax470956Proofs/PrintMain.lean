import Lax470956Proofs.PrintProg

/-!
The printer, assembled: the guard, the header, the three blocks of numbers, the matrix.
-/

namespace Lax470956Proofs.PrintMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956Proofs.PrintModel Lax470956Proofs.EmitNat Lax470956Proofs.PrintProg
open Lax470956.InstanceEncoding

variable {B : ℕ} {y : List ℕ}

/-- A block of numbers, with the context carried across. -/
theorem numLoop_ctx {S : ℕ} (hs : Small B S y) :
    Spec B (fun σ => PCtx y σ ∧ σ.vars "b" + jobCount y ≤ y.length) numLoop
      (fun σ σ' => PCtx y σ' ∧ σ'.out = σ.out ++ (List.range (jobCount y)).flatMap
        fun j => bitsNat (y.getD (σ.vars "b" + j) 0))
      ((48 * S + 60 + 4) * jobCount y + 6) := by
  intro σ ⟨hctx, hb⟩
  obtain ⟨σ', hrun, hout, hfv, hfa, -, -⟩ :=
    (numLoop_spec' (B := B) hs).frame σ ⟨hctx.1, hctx.2.2.1, hb⟩
  refine ⟨σ', hrun, hctx.congr (fun x hx => hfv x ?_) (hfa "a" (by simp [warrs_numLoop])), hout⟩
  rw [wvars_numLoop]
  simp only [pctxVars, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def blocks : Com :=
  .seq (.assign "b" (.lit 2)) (.seq numLoop
    (.seq (.assign "b" (add (.lit 2) (V "J"))) (.seq numLoop
      (.seq (.assign "b" (add (.lit 2) (mul (.lit 2) (V "J")))) numLoop))))

theorem blocks_spec {S : ℕ} (hs : Small B S y) (hg : Guard y) (KN : ℕ)
    (hKN : (48 * S + 60 + 4) * jobCount y + 6 = KN) :
    Spec B (fun σ => PCtx y σ) blocks
      (fun σ σ' => PCtx y σ' ∧ σ'.out = σ.out ++
        (List.range (jobCount y)).flatMap (fun j => bitsNat (proc y j)) ++
        (List.range (jobCount y)).flatMap (fun j => bitsNat (due y j)) ++
        (List.range (jobCount y)).flatMap (fun j => bitsNat (wt y j))) (3 * KN + 20) := by
  have hlen := hs.len
  have hg1 := hg.1
  have hn : Spec B _ numLoop _ KN := hKN ▸ (numLoop_ctx (B := B) hs)
  run_vcg [hn]
  all_goals simp only [PCtx, Env.setVar] at *
  all_goals simp at *
  all_goals first
    | omega
    | (simp_all [proc, due, wt, Nat.add_assoc]; done)
    | (simp_all [proc, due, wt, Nat.add_assoc]; omega)

/-- Writing a number, with the context carried across. -/
theorem emitNat_ctx (S : ℕ) :
    Spec B (fun σ => PCtx y σ ∧ σ.vars "v" + 4 < B ∧ (σ.vars "v").size ≤ S) emitNat
      (fun σ σ' => PCtx y σ' ∧ σ'.out = σ.out ++ bitsNat (σ.vars "v")) (48 * S + 40) := by
  intro σ ⟨hctx, hv⟩
  obtain ⟨σ', hrun, hout, hfv, hfa, -, -⟩ := (emitNat_spec (B := B) S).frame σ hv
  refine ⟨σ', hrun, hctx.congr (fun x hx => hfv x ?_) (hfa "a" (by simp [warrs_emitNat])), hout⟩
  rw [wvars_emitNat]
  simp only [pctxVars, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def headerNums : Com :=
  .seq (.assign "v" (V "J")) (.seq emitNat (.seq (.assign "v" (V "M")) emitNat))

theorem headerNums_spec {S : ℕ} (hs : Small B S y) (hg : Guard y) (KE : ℕ)
    (hKE : 48 * S + 40 = KE) :
    Spec B (fun σ => PCtx y σ) headerNums
      (fun σ σ' => PCtx y σ' ∧
        σ'.out = σ.out ++ bitsNat (jobCount y) ++ bitsNat (machineCount y)) (2 * KE + 10) := by
  have hlen := hs.len
  have hJ := hs.getD_lt 0
  have hM := hs.getD_lt 1
  have hJs := hs.getD_size 0
  have hMs := hs.getD_size 1
  have he : Spec B _ emitNat _ KE := hKE ▸ (emitNat_ctx (B := B) (y := y) S)
  run_vcg [he]
  all_goals simp only [PCtx, Env.setVar] at *
  all_goals simp at *
  all_goals first
    | omega
    | (simp_all [jobCount, machineCount]; done)
    | (simp_all [jobCount, machineCount]; omega)

def work : Com :=
  .seq (.assign "O0" (add (.lit 2) (mul (.lit 3) (V "J"))))
    (.seq (.assign "R" (sub (V "L") (V "T0"))) (.seq headerNums (.seq blocks mLoop)))

/-- What the guard leaves behind when it passes. -/
def W0 (y : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ σ.vars "J" = jobCount y ∧
    σ.vars "M" = machineCount y ∧ σ.vars "T0" = 3 + 4 * jobCount y ∧ σ.out = []

theorem work_spec {S : ℕ} (hs : Small B S y) (hg : Guard y) (KE KN KM : ℕ)
    (hKE : 48 * S + 40 = KE) (hKN : (48 * S + 60 + 4) * jobCount y + 6 = KN)
    (hKM : ((44 * room y + 6 + 30 + 4) * machineCount y + 6 + 30 + 4) * jobCount y + 6 = KM) :
    Spec B (fun σ => W0 y σ) work (fun _ σ' => σ'.out = print y)
      (2 * KE + 3 * KN + KM + 50) := by
  have hlen := hs.len
  have hg1 := hg.1
  have hm : Spec B _ mLoop _ KM := hKM ▸ (mLoop_spec (B := B) hs hg _ _ rfl rfl)
  run_vcg [headerNums_spec hs hg KE hKE, blocks_spec hs hg KN hKN, hm]
  all_goals simp only [W0, PCtx, Env.setVar] at *
  all_goals try simp at *
  all_goals first
    | omega
    | (exact ‹_ ∧ _›.1)
    | (simp_all [print, room]; done)
    | (simp_all [print, room]; omega)

theorem work_spec' {S : ℕ} (hs : Small B S y) (KE KN KM : ℕ)
    (hKE : 48 * S + 40 = KE) (hKN : (48 * S + 60 + 4) * jobCount y + 6 = KN)
    (hKM : ((44 * room y + 6 + 30 + 4) * machineCount y + 6 + 30 + 4) * jobCount y + 6 = KM) :
    Spec B (fun σ => W0 y σ ∧ Guard y) work (fun _ σ' => σ'.out = print y)
      (2 * KE + 3 * KN + KM + 50) :=
  fun σ h => work_spec hs h.2 KE KN KM hKE hKN hKM σ h.1

def guarded : Com :=
  .ite (.lt (.lit 1) (V "L"))
    (.seq (.assign "J" (.get "a" (.lit 0))) (.seq (.assign "M" (.get "a" (.lit 1)))
      (.ite (.lt (V "J") (V "L"))
        (.seq (.assign "T0" (add (.lit 3) (mul (.lit 4) (V "J"))))
          (.ite (.lt (V "L") (V "T0")) .skip (.ite (.lt (V "L") (V "M")) .skip work)))
        .skip)))
    .skip

theorem guarded_spec {S : ℕ} (hs : Small B S y) (KW : ℕ)
    (hKW : 2 * (48 * S + 40) + 3 * ((48 * S + 60 + 4) * jobCount y + 6) +
      (((44 * room y + 6 + 30 + 4) * machineCount y + 6 + 30 + 4) * jobCount y + 6) + 50 = KW) :
    Spec B (fun σ => σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ σ.out = []) guarded
      (fun _ σ' => σ'.out = print y) (KW + 40) := by
  have hlen := hs.len
  have hJ := hs.getD_lt 0
  have hM := hs.getD_lt 1
  have hw : Spec B _ work _ KW := hKW ▸ (work_spec' (B := B) hs _ _ _ rfl rfl rfl)
  run_vcg [hw]
  all_goals simp only [W0, Env.setVar] at *
  all_goals try simp at *
  all_goals first
    | omega
    | (simp_all; omega)
    | (simp_all [print, Guard, jobCount, machineCount]; done)
    | (simp_all [print, Guard, jobCount, machineCount]; omega)
    | (have hng : ¬ Guard y := (by simp_all [Guard, jobCount, machineCount]; try omega)
       simp_all [print])

/-- Off the guard the printer stops at once. -/
theorem guarded_spec_no {S : ℕ} (hs : Small B S y) (hng : ¬ Guard y) :
    Spec B (fun σ => σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ σ.out = []) guarded
      (fun _ σ' => σ'.out = print y) 40 := by
  have hlen := hs.len
  have hJ := hs.getD_lt 0
  have hM := hs.getD_lt 1
  have hw : Spec B (fun σ => W0 y σ ∧ Guard y) work (fun _ σ' => σ'.out = print y) 0 :=
    fun σ h => absurd h.2 hng
  run_vcg [hw]
  all_goals simp only [W0, Env.setVar] at *
  all_goals try simp at *
  all_goals first
    | omega
    | (simp_all; omega)
    | (simp_all [print]; done)
    | (exfalso; apply hng; simp_all [Guard, jobCount, machineCount]; done)
    | (exfalso; apply hng; simp_all [Guard, jobCount, machineCount]; omega)

def com : Com := .seq ReadAll.readAll guarded

end Lax470956Proofs.PrintMain
