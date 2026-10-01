import Lax470956Proofs.Construction1Passes
import Lax470956Proofs.Construction1Reduce
import Lax470956.Theorem1

/-!
Construction 1 as a word RAM program: the whole program, and its running time.
-/

namespace Lax470956Proofs.Construction1Main

open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer
open Lax470956.MulticolouredClique Lax470956.Construction1
open Lax470956Proofs.Construction1Shape Lax470956Proofs.Construction1Prog
open Lax470956Proofs.Construction1Read Lax470956Proofs.Construction1Tables
open Lax470956Proofs.Construction1Ctx Lax470956Proofs.Construction1Setup
open Lax470956Proofs.Construction1Info Lax470956Proofs.Construction1Passes

variable {x : List ℕ} {G : Instance}

/-- The header of the emitted word, and the prefixes each pass starts from. -/
noncomputable def pre0 (G : Instance) : List ℕ := [nJobs G, nMach G]
noncomputable def pre1 (G : Instance) : List ℕ := pre0 G ++ procBlock G
noncomputable def pre2 (G : Instance) : List ℕ := pre1 G ++ dueBlock G
noncomputable def pre3 (G : Instance) : List ℕ := pre2 G ++ wtBlock G
noncomputable def pre4 (G : Instance) : List ℕ := pre3 G ++ offBlock G

theorem com_spec (hR : Reads x G) :
    Spec (bnd x G)
      (fun σ => σ.inp = vn x :: ve x :: body x ∧ σ.out = [] ∧
        (σ.arrs "a").length = (body x).length ∧ Tables x σ)
      com (fun _ σ' => σ'.out = emit G)
      (12 * (body x).length + 44 * (vn x * kk x) + 64 * (vn x + 2 * ve x)
        + 1640 * nJobs G + 1000) := by
  have hsm := (big hR).small
  have hM := nMach_lt_bnd hR
  have hW := tw_lt_bnd (x := x) (G := G)
  run_vcg [setup_spec hR, procLoop_spec hR (pre0 G), dueLoop_spec hR (pre1 G),
    wtLoop_spec hR (pre2 G), offLoop_spec hR (pre3 G), tgtLoop_spec hR (pre4 G)]
  · obtain ⟨⟨hctx, -, hout⟩, hj⟩ := ‹TInv x G (pre4 G) _ ∧ _›
    have hWv : _ = targetWeight G := hctx.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [hout, hj, hWv]
    simp [emit, pre0, pre1, pre2, pre3, pre4, tgtBlock]
  · exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩
  · obtain ⟨hctx, -⟩ := ‹Ctx x G _ ∧ _›
    rw [nJ_of_ctx hctx]; omega
  · obtain ⟨hctx, -⟩ := ‹Ctx x G _ ∧ _›
    have hMv : _ = nMach G := hctx.2.2.2.2.2.2.2.1
    simp only [hMv]; exact hM
  · obtain ⟨hctx, hout⟩ := ‹Ctx x G _ ∧ _›
    have hMv : _ = nMach G := hctx.2.2.2.2.2.2.2.1
    refine ⟨(Ctx.of_write (Ctx.of_write hctx _) _).setVar _ _ (by decide), by simp, ?_⟩
    simp [hout, pre0, nJ_of_ctx hctx, hMv]
  · obtain ⟨⟨hctx, -, hout⟩, hj⟩ := ‹BInv x G (nJobs G) (pre0 G) (procOf G) _ ∧ _›
    refine ⟨hctx.setVar _ _ (by decide), by simp, ?_⟩
    simp [hout, hj, pre1, procBlock]
  · obtain ⟨⟨hctx, -, hout⟩, hj⟩ := ‹BInv x G (nJobs G) (pre1 G) (dueOf G) _ ∧ _›
    refine ⟨hctx.setVar _ _ (by decide), by simp, ?_⟩
    simp [hout, hj, pre2, dueBlock]
  · obtain ⟨⟨hctx, -, hout⟩, hj⟩ := ‹BInv x G (nJobs G) (pre2 G) (wtOf G) _ ∧ _›
    refine ⟨(hctx.setVar _ _ (by decide)).setVar _ _ (by decide), by simp, ?_, ?_⟩
    · intro _; simp [offOf]
    · simp [hout, hj, pre3, wtBlock]
  · obtain ⟨⟨hctx, -, -, hout⟩, hj⟩ := ‹OInv x G (pre3 G) _ ∧ _›
    refine ⟨hctx.setVar _ _ (by decide), by simp, ?_⟩
    simp [hout, hj, pre4, offBlock]
  · obtain ⟨⟨hctx, -, -⟩, -⟩ := ‹TInv x G (pre4 G) _ ∧ _›
    have hWv : _ = targetWeight G := hctx.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [hWv]; omega

/-! ### From the Specification to the Machine -/

open Classical in
/-- The instance a word is read as, and an arbitrary one for a word that is none. -/
noncomputable def Gof (x : List ℕ) : Instance :=
  if h : ∃ G, EncodesInstance x G then h.choose
  else ⟨0, 0, ⊥, fun v => v.elim0, fun u => u.elim0⟩

lemma encodes_Gof {x : List ℕ} (h : ∃ G, EncodesInstance x G) : EncodesInstance x (Gof x) := by
  rw [Gof, dif_pos h]; exact h.choose_spec

lemma reduce_eq {x : List ℕ} (h : ∃ G, EncodesInstance x G) : reduce x = emit (Gof x) := by
  rw [Lax470956Proofs.Construction1Reduce.reduce_pos h, Gof, dif_pos h]

/-- The array lengths the program needs. -/
def extOf (x : List ℕ) : String → ℕ := fun a =>
  if a = "a" then (body x).length else if a = "r" then vn x else 2 * ve x

/-- The cost of the whole program, in IMP+ units. -/
noncomputable def Kc (x : List ℕ) : ℕ :=
  12 * (body x).length + 44 * (vn x * kk x) + 64 * (vn x + 2 * ve x)
    + 1640 * nJobs (Gof x) + 1000

theorem solves :
    Solves layout com Instances reduce (fun x => bnd x (Gof x)) Kc where
  ok := com_ok
  inp := fun x _ v hv => entry_lt_bnd hv
  run := by
    intro x hx
    have hR := reads_of_encodes (encodes_Gof hx)
    have hpre : (initEnv (extOf x) x).inp = vn x :: ve x :: body x ∧
        (initEnv (extOf x) x).out = [] ∧
        ((initEnv (extOf x) x).arrs "a").length = (body x).length ∧
        Tables x (initEnv (extOf x) x) := by
      refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
      · show x = _
        exact head_shape hR
      all_goals simp [initEnv, extOf]
    obtain ⟨σ', hrun, hout⟩ := com_spec hR _ hpre
    exact ⟨extOf x, σ', hrun, by rw [hout, reduce_eq hx]⟩

open Lax470956.ParameterizedComplexity in
/-- The largest entry of a nonempty fitting word fits with the length. -/
lemma fits_max {c w : ℕ} {y : List ℕ} (hne : y ≠ []) (h : Fits c w y) :
    c * (y.length + y.foldr max 0 + 1) ≤ 2 ^ w := by
  rcases Lax470956Proofs.Pmax.foldr_max_mem_or_zero y with hm | hm
  · exact h _ hm
  · rw [hm]
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    have := h a List.mem_cons_self
    have h1 : c * ((a :: t).length + 0 + 1) ≤ c * ((a :: t).length + a + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-- The time bound's function of the parameter. -/
def gOf (k : ℕ) : ℕ := (k + 1) * (k + 1)

open Lax470956.ParameterizedComplexity in
/-- **Construction 1, end to end.** -/
theorem prog_computesInTime (w : ℕ) :
    ComputesInTime w prog
      {x | x ∈ Instances ∧ Fits 70000 w x ∧ Fits 70000 w (reduce x)}
      reduce (fun x => 70000 * gOf (x.getLast?.getD 0) * (x.length + 1)) := by
  have hs : Solves layout com
      {x | x ∈ Instances ∧ Fits 70000 w x ∧ Fits 70000 w (reduce x)} reduce
      (fun x => bnd x (Gof x)) Kc :=
    ⟨solves.ok, fun y hy => solves.inp y hy.1, fun y hy => solves.run y hy.1⟩
  refine computesInTime_of_solves hs (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨hx, hf1, hf2⟩ := hy
    have hR := reads_of_encodes (encodes_Gof hx)
    rw [reduce_eq hx] at hf2
    have hne : y ≠ [] := by
      intro h; have := hR.length_eq; rw [h] at this; simp at this; omega
    have h1 := fits_max hne hf1
    have h2 : 70000 * ((emit (Gof y)).length + targetWeight (Gof y) + 1) ≤ 2 ^ w :=
      hf2 _ (by simp [emit])
    refine fitsWords_of_max_le (by simp only [bnd]; omega) ?_
    simp only [Layout.span, layout, List.length_cons, List.length_nil, bnd, max_le_iff]
    omega
  · obtain ⟨hx, -, -⟩ := hy
    have hG := encodes_Gof hx
    have hR := reads_of_encodes hG
    have hk : y.getLast?.getD 0 = (Gof y).colours := Lax470956Proofs.MccTransfer.param_eq hG
    have hbig := big hR
    have hlen := hR.length_eq
    have hbl := body_length hR
    have hE : nEJob (Gof y) ≤ 2 * ve y := by rw [← hbig.accLen]; exact acc_length_le _ _
    rw [const_eq, hk]
    simp only [Kc, gOf, nJobs, nVJob, nCJob]
    rw [hbig.vn_eq, hbig.kk_eq] at *
    set n := (Gof y).vertices
    set k := (Gof y).colours
    set t := (k + 1) * (k + 1) * (y.length + 1) with ht
    have hg1 : 1 ≤ (k + 1) * (k + 1) := Nat.mul_pos (by omega) (by omega)
    have hgk : k ≤ (k + 1) * (k + 1) := by nlinarith
    have hgkk : k * k ≤ (k + 1) * (k + 1) := by nlinarith
    have hX : y.length + 1 ≤ t := Nat.le_mul_of_pos_left _ hg1
    have hnX : n ≤ y.length + 1 := by omega
    have h1 : n * k ≤ t := by
      rw [ht, Nat.mul_comm n k]; exact Nat.mul_le_mul hgk hnX
    have h2 : k * k * n ≤ t := Nat.mul_le_mul hgkk hnX
    have hT : 70000 * ((k + 1) * (k + 1)) * (y.length + 1) = 70000 * t := by
      rw [ht]; ring
    rw [hT]
    omega

open Lax470956.ParameterizedComplexity in
/--
---
conclusion: Lax470956.Theorem1.mcc_fptReduces_byMachines
---
The reduction is Construction 1 as a map on words. It sends instances to instances and
preserves and reflects yes-instances because the construction is correct and its word
encodes it; the image has one machine per pair of colours and one more, a function of
the number of colours alone; and it is computed by one word RAM program.

The program copies the word into an array, ranks the vertices in the paper's order by
sweeping them once per colour, enumerates the edges by one scan of the target array
with a pointer to the vertex owning the current slot, and then writes the six blocks of
the instance encoding and the threshold, one counted pass per block. Every pass
recomputes the numbers of job `j` through one shared command, so the construction's
arithmetic is verified once. The sweep costs `k · n` steps and each pass a constant per
job, and there are at most `(k + k² + 1)(n + 2m)` jobs, so the whole is within
`70000 · (k + 1)² · (|x| + 1)` machine instructions.
-/
theorem mcc_fptReduces_byMachines :
    Lax470956.MulticolouredClique.problem ≤fpt Lax470956.SchedulingProblems.byMachines :=
  ⟨reduce, prog, 70000, gOf, fun k => k.choose 2 + 1,
    { maps_domain := fun x _ => Lax470956Proofs.Construction1Reduce.reduce_maps x
      correct := fun x _ => Lax470956Proofs.Construction1Reduce.reduce_correct x
      param_le := fun x _ => Lax470956Proofs.Construction1Reduce.reduce_param x
      time := fun w => prog_computesInTime w }⟩

end Lax470956Proofs.Construction1Main
