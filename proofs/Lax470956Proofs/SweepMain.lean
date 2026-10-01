import Lax470956Proofs.SweepOrder
import Lax470956Proofs.Pmax
import Lax470956.SchedulingProblems

/-!
Theorem 3's program, assembled: the header, then the eight passes, then the answer.
-/

namespace Lax470956Proofs.SweepMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.Scheduling Lax470956.Scheduling.Instance Lax470956.Preprocessing
open Lax470956.InstanceEncoding Lax470956.SchedulingProblems
open Lax470956.DynamicProgram (optimum)
open Lax470956.ParameterizedComplexity (Fits)
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax470956Proofs.FreeDP Lax470956Proofs.SweepProg Lax470956Proofs.SweepBody
open Lax470956Proofs.SweepPre Lax470956Proofs.SweepOrder Lax470956Proofs.SweepLoop
open Lax470956Proofs.SweepTable Lax470956Proofs.BlockWalk
open Lax470956Proofs.ReadHdr (readWord readWord_spec)

variable {B : ℕ} {x : List ℕ}

/-! ### The Word Determines the Instance -/

lemma encodes_unique {y : List ℕ} {I I' : Instance} (h : EncodesInstance y I)
    (h' : EncodesInstance y I') : I = I' := by
  obtain ⟨jb, mc, p, d, w, el, hpp, hpd⟩ := I
  obtain ⟨jb', mc', p', d', w', el', hpp', hpd'⟩ := I'
  have hj : jb = jb' := by
    have a1 := h.jobCount_eq; have a2 := h'.jobCount_eq; simp at a1 a2; omega
  subst hj
  have hm : mc = mc' := by
    have a1 := h.machineCount_eq; have a2 := h'.machineCount_eq; simp at a1 a2; omega
  subst hm
  have hpe : p = p' := funext fun j => by
    have a1 := h.proc_eq j; have a2 := h'.proc_eq j; simp at a1 a2; omega
  have hde : d = d' := funext fun j => by
    have a1 := h.due_eq j; have a2 := h'.due_eq j; simp at a1 a2; omega
  have hwe : w = w' := funext fun j => by
    have a1 := h.wt_eq j; have a2 := h'.wt_eq j; simp at a1 a2; omega
  have hel : el = el' := funext fun j => Finset.ext fun i => by
    have a1 := h.eligible_iff j i; have a2 := h'.eligible_iff j i
    simp only at a1 a2
    rw [a1, a2]
  subst hpe; subst hde; subst hwe; subst hel
  rfl

lemma decision_unique {x : List ℕ} {I I' : Instance} {W W' : ℕ}
    (h : EncodesDecisionInstance x I W) (h' : EncodesDecisionInstance x I' W') :
    I = I' ∧ W = W' := by
  obtain ⟨y, hxy, hy⟩ := h
  obtain ⟨y', hxy', hy'⟩ := h'
  have hlen : y.length = y'.length := by
    have : (y ++ [W]).length = (y' ++ [W']).length := by rw [← hxy, ← hxy']
    simpa using this
  obtain ⟨he1, he2⟩ := List.append_inj (show y ++ [W] = y' ++ [W'] from by rw [← hxy, hxy'])
    hlen
  subst he1
  exact ⟨encodes_unique hy hy', by simpa using he2⟩

/-! ### The Threshold Is Met Exactly When It Is at Most the Optimum -/

lemma hasWeight_iff (I : Instance) (W : ℕ) : I.HasWeight W ↔ W ≤ optimum I := by
  constructor
  · rintro ⟨σ, hf, hw⟩
    exact le_trans hw (Finset.le_sup (f := Instance.weight)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩))
  · intro h
    have hne : (Finset.univ.filter fun σ : I.Schedule => Feasible σ).Nonempty :=
      ⟨fun _ => none, Finset.mem_filter.mpr ⟨Finset.mem_univ _, feasible_none⟩⟩
    obtain ⟨σ, hmem, heq⟩ := Finset.exists_mem_eq_sup _ hne Instance.weight
    refine ⟨σ, (Finset.mem_filter.mp hmem).2, ?_⟩
    rw [optimum, heq] at h
    exact h

/-! ### What the Decision Word Says -/

lemma getD_app_left {y : List ℕ} {W i : ℕ} (h : i < y.length) :
    (y ++ [W]).getD i 0 = y.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

/-- Everything the sweep needs of the decision word, read off the instance word. -/
theorem enc_of_decision {x : List ℕ} {I : Instance} {W : ℕ}
    (h : EncodesDecisionInstance x I W) :
    Enc I x ∧ x.length = 3 + 4 * I.jobs + offset x I.jobs + 1 ∧
      machineCount x = I.machines ∧ x.getD (x.length - 1) 0 = W := by
  obtain ⟨y, rfl, hy⟩ := h
  have hylen : y.length = 3 + 4 * I.jobs + offset y I.jobs := hy.length_eq
  have hjc : jobCount (y ++ [W]) = I.jobs := by
    rw [jobCount, getD_app_left (by omega)]; exact hy.jobCount_eq
  have hoff : ∀ i, i ≤ I.jobs → offset (y ++ [W]) i = offset y i := by
    intro i hi
    rw [offset, offset, hjc, hy.jobCount_eq, getD_app_left (by omega)]
  have htgt : ∀ t, t < offset y I.jobs → target (y ++ [W]) t = target y t := by
    intro t ht
    rw [target, target, hjc, hy.jobCount_eq, getD_app_left (by omega)]
  have hoffj : offset (y ++ [W]) I.jobs = offset y I.jobs := hoff I.jobs (le_refl _)
  refine ⟨⟨hjc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hoffj]; simp; omega
  · intro j
    rw [proc, getD_app_left (show 2 + j.val < y.length from by have := j.isLt; omega),
      ← hy.proc_eq j, proc]
  · intro j
    rw [due, hjc, getD_app_left (show 2 + I.jobs + j.val < y.length from by
      have := j.isLt; omega), ← hy.due_eq j, due, hy.jobCount_eq]
  · intro j
    rw [wt, hjc, getD_app_left (show 2 + 2 * I.jobs + j.val < y.length from by
      have := j.isLt; omega), ← hy.wt_eq j, wt, hy.jobCount_eq]
  · rw [hoff 0 (by omega)]; exact hy.offset_zero
  · intro j hj
    rw [hoff j (by omega), hoff (j + 1) (by omega)]
    exact hy.offset_mono j hj
  · intro t ht
    rw [hoffj] at ht
    rw [htgt t ht]
    exact hy.target_lt t ht
  · intro j i
    rw [hy.eligible_iff j i]
    constructor
    · rintro ⟨t, h1, h2, h3⟩
      refine ⟨t, ?_, ?_, ?_⟩
      · rw [hoff j (le_of_lt j.isLt)]; exact h1
      · rw [hoff (j.val + 1) (by omega)]; exact h2
      · rw [htgt t (by
          have := hy.offset_mono j.val j.isLt
          have hle : offset y (j.val + 1) ≤ offset y I.jobs :=
            (Enc.off_mono' ⟨hy.jobCount_eq, by omega, hy.proc_eq, hy.due_eq, hy.wt_eq,
              hy.offset_zero, hy.offset_mono, hy.target_lt, hy.eligible_iff⟩)
              I.jobs (le_refl _) _ j.isLt
          omega)]
        exact h3
    · rintro ⟨t, h1, h2, h3⟩
      rw [hoff j (le_of_lt j.isLt)] at h1
      rw [hoff (j.val + 1) (by omega)] at h2
      have hlt : t < offset y I.jobs := by
        have hle : offset y (j.val + 1) ≤ offset y I.jobs :=
          (Enc.off_mono' ⟨hy.jobCount_eq, by omega, hy.proc_eq, hy.due_eq, hy.wt_eq,
            hy.offset_zero, hy.offset_mono, hy.target_lt, hy.eligible_iff⟩)
            I.jobs (le_refl _) _ j.isLt
        omega
      rw [htgt t hlt] at h3
      exact ⟨t, h1, h2, h3⟩
  · rw [hoffj]; simp; omega
  · rw [machineCount, getD_app_left (by omega)]; exact hy.machineCount_eq
  · simp only [List.length_append, List.length_cons, List.length_nil]
    rw [show y.length + 1 - 1 = y.length from by omega,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp

/-! ### The Header -/

theorem header_spec (n m W : ℕ) (hx : ∀ i, x.getD i 0 + 2 < B) (hxB : x.length + 2 < B)
    (hlen : 3 + 4 * n ≤ x.length) (hjc : x.getD 0 0 = n) (hmc : x.getD 1 0 = m)
    (hW : x.getD (x.length - 1) 0 = W) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length) header
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.vars "m" = m ∧ σ'.vars "W" = W ∧
        σ'.vars "cap" = W ∧ σ'.vars "O0" = 2 + 3 * n ∧ σ'.vars "T0" = 3 + 4 * n) 25 := by
  intro σ ⟨ha, hL⟩
  have hnB : n + 2 < B := by rw [← hjc]; exact hx 0
  have hmB : m + 2 < B := by rw [← hmc]; exact hx 1
  have hWB : W + 2 < B := by rw [← hW]; exact hx _
  have haL : (σ.arrs "a").length = x.length := by rw [ha]
  have hxpos : 0 < x.length := by omega
  have e1 : (Expr.get "a" (lit 0)).evalB B σ = some n :=
    ReadHdr.evalB_getE (ReadHdr.evalB_lit (by omega)) (by omega) (by omega) (by rw [ha]; exact hjc)
  have e2 : (Expr.get "a" (lit 1)).evalB B (σ.setVar "n" n) = some m :=
    ReadHdr.evalB_getE (ReadHdr.evalB_lit (by omega)) (by omega) (by simp [Env.setVar]; omega)
      (by simp only [Env.setVar]; rw [ha]; exact hmc)
  have e3 : (Expr.get "a" (sub (V "L") (lit 1))).evalB B
      ((σ.setVar "n" n).setVar "m" m) = some W := by
    refine ReadHdr.evalB_getE (ReadHdr.evalB_sub (ReadHdr.evalB_var ?_) (ReadHdr.evalB_lit (by omega)) ?_) (by omega) ?_ ?_
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte, hL]; omega
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte, hL]; omega
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte, hL]; omega
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte, hL]
      rw [ha]; exact hW
  have e4 : (V "W").evalB B (((σ.setVar "n" n).setVar "m" m).setVar "W" W) = some W := by
    have := ReadHdr.evalB_var (B := B) (σ := ((σ.setVar "n" n).setVar "m" m).setVar "W" W)
      (y := "W") (by simp [Env.setVar]; omega)
    simpa [Env.setVar] using this
  have e5 : (add (lit 2) (mul (lit 3) (V "n"))).evalB B
      ((((σ.setVar "n" n).setVar "m" m).setVar "W" W).setVar "cap" W)
      = some (2 + 3 * n) := by
    have h := ReadHdr.evalB_add (B := B)
      (σ := (((σ.setVar "n" n).setVar "m" m).setVar "W" W).setVar "cap" W)
      (ReadHdr.evalB_lit (show (2 : ℕ) < B by omega))
      (ReadHdr.evalB_mul (ReadHdr.evalB_lit (show (3 : ℕ) < B by omega))
        (ReadHdr.evalB_var (y := "n") (by simp [Env.setVar]; omega))
        (by simp [Env.setVar]; omega))
      (by simp [Env.setVar]; omega)
    simpa [Env.setVar] using h
  have e6 : (add (lit 3) (mul (lit 4) (V "n"))).evalB B
      (((((σ.setVar "n" n).setVar "m" m).setVar "W" W).setVar "cap" W).setVar "O0"
        (2 + 3 * n)) = some (3 + 4 * n) := by
    have h := ReadHdr.evalB_add (B := B)
      (σ := ((((σ.setVar "n" n).setVar "m" m).setVar "W" W).setVar "cap" W).setVar "O0"
        (2 + 3 * n))
      (ReadHdr.evalB_lit (show (3 : ℕ) < B by omega))
      (ReadHdr.evalB_mul (ReadHdr.evalB_lit (show (4 : ℕ) < B by omega))
        (ReadHdr.evalB_var (y := "n") (by simp [Env.setVar]; omega))
        (by simp [Env.setVar]; omega))
      (by simp [Env.setVar]; omega)
    simpa [Env.setVar] using h
  refine ⟨((((((σ.setVar "n" n).setVar "m" m).setVar "W" W).setVar "cap" W).setVar "O0"
      (2 + 3 * n)).setVar "T0" (3 + 4 * n)),
    (Run.seq (Run.assign e1) (Run.seq (Run.assign e2) (Run.seq (Run.assign e3)
      (Run.seq (Run.assign e4) (Run.seq (Run.assign e5) (Run.assign e6)))))).mono
      (by norm_num [Expr.size]), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar]

/-! ### Numeric Facts About the Word -/

/-- The largest entry. -/
def mxE (x : List ℕ) : ℕ := x.foldr max 0

lemma getD_le_mxE (x : List ℕ) (i : ℕ) : x.getD i 0 ≤ mxE x := by
  by_cases h : i < x.length
  · refine Lax470956Proofs.Pmax.le_foldr_max ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.getElem_mem _
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

lemma pmaxAux_le_mxE (x : List ℕ) : ∀ N, pmaxAux x N ≤ mxE x := by
  intro N
  induction N with
  | zero => simp [pmaxAux]
  | succ N ih =>
      rw [pmaxAux_succ]
      exact max_le ih (by simpa [proc] using getD_le_mxE x (2 + N))

lemma pmaxOf_le_mxE (x : List ℕ) : pmaxOf x ≤ mxE x := pmaxAux_le_mxE x _

lemma sum_bodyCost (m S n T : ℕ) (f : ℕ → ℕ)
    (hf : ∑ j ∈ Finset.range n, f j = T) :
    ∑ j ∈ Finset.range n, bodyCost m S (f j)
      = n * ((44 * m + 148) * S + 117) + (84 * S + 24) * T := by
  simp only [bodyCost]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    show (∑ j ∈ Finset.range n, (84 * S + 24) * f j) = (84 * S + 24) * T by
      rw [← Finset.mul_sum, hf]]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

lemma lt_pow_self {P m : ℕ} (hm : 0 < m) : P < (P + 1) ^ m := by
  calc P < P + 1 := by omega
    _ = (P + 1) ^ 1 := (pow_one _).symm
    _ ≤ (P + 1) ^ m := Nat.pow_le_pow_right (by omega) hm

/-! ### The State the Passes Start from -/

/-- The arrays, as the initial environment leaves them. -/
structure Fresh (n m S Lo : ℕ) (σ : Env) : Prop where
  lpw : m ≤ (σ.arrs "pw").length
  locc : Lo ≤ (σ.arrs "occ").length
  lfj : Lo ≤ (σ.arrs "fj").length
  lst : Lo ≤ (σ.arrs "st").length
  lnx2 : Lo ≤ (σ.arrs "nx2").length
  lnj : n ≤ (σ.arrs "nj").length
  lord : n ≤ (σ.arrs "ord").length
  ldl : n ≤ (σ.arrs "dl").length
  lnc : n ≤ (σ.arrs "nc").length
  lV : (σ.arrs "V").length = S
  lV2 : (σ.arrs "V2").length = S
  lVt : (σ.arrs "Vt").length = S
  zocc : ∀ d, (σ.arrs "occ").getD d 0 = 0
  zfj : ∀ d, (σ.arrs "fj").getD d 0 = 0

/-! ### The Numeric Facts Every Pass Runs Under -/

variable {Lo : ℕ}

/-- Everything the passes need to know about the sizes. -/
structure Sizes (B : ℕ) (x : List ℕ) (I : Instance) (W Lo : ℕ) : Prop where
  dec : EncodesDecisionInstance x I W
  mpos : 0 < I.machines
  npos : 0 < I.jobs
  big : 4 * ((pmaxOf x + 1) ^ I.machines + 2 * mxE x + x.length) + 64 ≤ B
  lo : B ≤ Lo

namespace Sizes

variable {I : Instance} {W : ℕ}

lemma enc (h : Sizes B x I W Lo) : Enc I x := (enc_of_decision h.dec).1
lemma xlen (h : Sizes B x I W Lo) : x.length = 3 + 4 * I.jobs + offset x I.jobs + 1 := (enc_of_decision h.dec).2.1
lemma mc (h : Sizes B x I W Lo) : machineCount x = I.machines := (enc_of_decision h.dec).2.2.1
lemma wv (h : Sizes B x I W Lo) : x.getD (x.length - 1) 0 = W := (enc_of_decision h.dec).2.2.2

lemma jc (h : Sizes B x I W Lo) : jobCount x = I.jobs := h.enc.jc

lemma xg (h : Sizes B x I W Lo) (i : ℕ) : x.getD i 0 + 2 < B := by
  have := getD_le_mxE x i; have := h.big; omega

lemma lenx (h : Sizes B x I W Lo) : x.length + 2 < B := by have := h.big; omega

lemma sB (h : Sizes B x I W Lo) : (pmaxOf x + 1) ^ I.machines + 2 < B := by have := h.big; omega

lemma pmxE (h : Sizes B x I W Lo) : pmaxOf x ≤ mxE x := pmaxOf_le_mxE x

lemma pB (h : Sizes B x I W Lo) : pmaxOf x + 2 < B := by have := h.pmxE; have := h.big; omega

lemma nB (h : Sizes B x I W Lo) : I.jobs + 2 < B := by
  have h1 : I.jobs = x.getD 0 0 := by rw [← h.jc]; rfl
  have := h.xg 0; omega

lemma mB (h : Sizes B x I W Lo) : I.machines + 2 < B := by
  have h1 : I.machines = x.getD 1 0 := by rw [← h.mc]; rfl
  have := h.xg 1; omega

lemma wB (h : Sizes B x I W Lo) : W + 2 < B := by rw [← h.wv]; exact h.xg _

lemma nlex (h : Sizes B x I W Lo) : 2 + I.jobs + I.jobs ≤ x.length := by have := h.xlen; omega

lemma dueE (h : Sizes B x I W Lo) (j : ℕ) (hj : j < I.jobs) : due x j = I.d ⟨j, hj⟩ := h.enc.due_eq ⟨j, hj⟩

lemma dueMx (h : Sizes B x I W Lo) (j : ℕ) : due x j ≤ mxE x := getD_le_mxE x _

lemma occ_true (h : Sizes B x I W Lo) {j : ℕ} (hj : j < I.jobs) : occB x I.jobs (due x j) = true := by
  have hm : j ∈ jlist (due x) (due x j) I.jobs :=
    (jlist_mem (due x) (due x j) I.jobs j).mpr ⟨hj, rfl⟩
  have hne : jlist (due x) (due x j) I.jobs ≠ [] := by intro hc; rw [hc] at hm; simp at hm
  simp [occB, List.isEmpty_iff, hne]

lemma occ_mem (h : Sizes B x I W Lo) {d : ℕ} (hd : occB x I.jobs d = true) : ∃ j, j < I.jobs ∧ due x j = d := by
  simp only [occB, Bool.not_eq_true'] at hd
  rcases hl : jlist (due x) d I.jobs with _ | ⟨b, l⟩
  · rw [hl] at hd; simp [List.isEmpty] at hd
  · have := (jlist_mem (due x) d I.jobs b).mp (by rw [hl]; exact List.mem_cons_self)
    exact ⟨b, this.1, this.2⟩

lemma occ_mxE (h : Sizes B x I W Lo) {d : ℕ} (hd : occB x I.jobs d = true) : d ≤ mxE x := by
  obtain ⟨j, -, rfl⟩ := h.occ_mem hd
  exact h.dueMx j

lemma occ0 (h : Sizes B x I W Lo) : occB x I.jobs 0 = false := by
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  obtain ⟨j, hj, hd⟩ := h.occ_mem hc
  have h1 := h.dueE j hj
  have h2 := I.p_le_d ⟨j, hj⟩
  have h3 := I.p_pos ⟨j, hj⟩
  omega

lemma pPos (h : Sizes B x I W Lo) : 0 < pmaxOf x := by
  have h1 : proc x 0 ≤ pmaxAux x (jobCount x) := pmaxAux_ge x _ 0 (by rw [h.jc]; exact h.npos)
  have h2 : proc x 0 = I.p ⟨0, h.npos⟩ := h.enc.proc_eq ⟨0, h.npos⟩
  have h3 := I.p_pos ⟨0, h.npos⟩
  rw [h2] at h1
  have : (0 : ℕ) < pmaxAux x (jobCount x) := lt_of_lt_of_le h3 h1
  rw [pmaxAux_jobCount] at this
  exact this

lemma pjP (h : Sizes B x I W Lo) (j : Fin I.jobs) : I.p j ≤ pmaxOf x := by
  have h1 : proc x j.val ≤ pmaxAux x (jobCount x) :=
    pmaxAux_ge x _ j.val (by rw [h.jc]; exact j.isLt)
  rw [h.enc.proc_eq j] at h1
  exact h1

end Sizes

/-! ### The Main Pass -/

set_option maxHeartbeats 2000000 in
theorem mainWork_spec {I : Instance} {W : ℕ} (hs : Sizes B x I W Lo) :
    Spec B (fun σ => Fresh I.jobs I.machines ((pmaxOf x + 1) ^ I.machines) Lo σ ∧
        σ.arrs "a" = x ∧ σ.out = [] ∧
        σ.vars "n" = I.jobs ∧ σ.vars "m" = I.machines ∧ σ.vars "W" = W ∧
        σ.vars "cap" = W ∧ σ.vars "O0" = 2 + 3 * I.jobs ∧ σ.vars "T0" = 3 + 4 * I.jobs)
      mainWork
      (fun _ σ' => σ'.out = [if W ≤ optimum I then 1 else 0])
      (1000 * ((pmaxOf x + 1) ^ I.machines * ((I.machines + 1) * (x.length + 1)))) := by
  classical
  set n := I.jobs with hndef
  set m := I.machines with hmdef
  set P := pmaxOf x with hPdef
  set S := (P + 1) ^ m with hSdef
  have hbig : 4 * (S + 2 * mxE x + x.length) + 64 ≤ B := by
    rw [hSdef, hPdef, hmdef]; exact hs.big
  have hB2 : 2 < B := by omega
  have hxg := hs.xg
  have hxB := hs.lenx
  have hnB : n + 2 < B := by rw [hndef]; exact hs.nB
  have hmB : m + 2 < B := by rw [hmdef]; exact hs.mB
  have hpB : P + 2 < B := by rw [hPdef]; exact hs.pB
  have hsB : S + 2 < B := by rw [hSdef, hPdef, hmdef]; exact hs.sB
  have hjc : jobCount x = n := by rw [hndef]; exact hs.jc
  have hnlex : 2 + n + n ≤ x.length := by rw [hndef]; exact hs.nlex
  have hmx : P ≤ mxE x := by rw [hPdef]; exact hs.pmxE
  have hlo := hs.lo
  have hdueL : ∀ j, j < n → due x j + P + 1 ≤ Lo := by
    intro j _; have := hs.dueMx j; omega
  have hdueB : ∀ j, j < n → due x j + P + 2 < B := by
    intro j _; have := hs.dueMx j; omega
  intro σ ⟨hfr, hax, houtx, hnv, hmv, hWv, hcapv, hO0v, hT0v⟩
  -- the largest processing time
  obtain ⟨σ1, hr1, ⟨ha1, hn1, hP1, -⟩, hfv1, hfa1, -, ho1⟩ :=
    (pmaxLoop_spec (B := B) (x := x) (n := n) hxg hB2 hnB (by omega) hjc).frame σ
      ⟨hax, hnv⟩
  have hnm1 : σ1.vars "m" = m := by
    rw [hfv1 "m" (by simp [pmaxLoop, pmaxBody, Com.wvars])]; exact hmv
  have harr1 : ∀ a, σ1.arrs a = σ.arrs a := fun a =>
    hfa1 a (by simp [pmaxLoop, pmaxBody, Com.warrs])
  -- the powers
  obtain ⟨σ2, hr2, ⟨hm2, hP2, hS2, hpw2, -⟩, hfv2, hfa2, -, ho2⟩ :=
    (powLoop_spec (B := B) (m := m) (P := P) (by rw [← hSdef]; exact hsB) hmB hpB).frame σ1
      ⟨hnm1, hP1, by rw [harr1]; exact hfr.lpw⟩
  have hfv2' : ∀ y, y ∉ ["S", "i"] → σ2.vars y = σ1.vars y := fun y hy =>
    hfv2 y (by simp [powLoop, powBody, Com.wvars] at hy ⊢; tauto)
  have harr2 : ∀ a, a ≠ "pw" → σ2.arrs a = σ1.arrs a := fun a ha =>
    hfa2 a (by simp [powLoop, powBody, Com.warrs]; exact ha)
  have ha2 : σ2.arrs "a" = x := by rw [harr2 "a" (by decide), harr1]; exact hax
  have hn2 : σ2.vars "n" = n := by
    rw [hfv2' "n" (by decide), hfv1 "n" (by simp [pmaxLoop, pmaxBody, Com.wvars])]; exact hnv
  -- the jobs of each deadline
  obtain ⟨σ3, hr3, ⟨ha3, hn3, hfj3, hocc3, hnj3, hnjL3⟩, hfv3, hfa3, -, ho3⟩ :=
    (bucketLoop_spec (B := B) (x := x) (n := n) Lo hxg hB2 hnB hxB hnlex hjc
      (fun j _ => by have := hs.dueMx j; omega)).frame σ2
      ⟨ha2, hn2, by rw [harr2 "occ" (by decide), harr1]; exact hfr.locc,
        by rw [harr2 "fj" (by decide), harr1]; exact hfr.lfj,
        by rw [harr2 "nj" (by decide), harr1]; exact hfr.lnj,
        by rw [harr2 "fj" (by decide), harr1]; exact hfr.zfj,
        by rw [harr2 "occ" (by decide), harr1]; exact hfr.zocc⟩
  have hfv3' : ∀ y, y ∉ ["j", "dd"] → σ3.vars y = σ2.vars y := fun y hy =>
    hfv3 y (by simp [bucketLoop, bucketBody, Com.wvars] at hy ⊢; tauto)
  have harr3 : ∀ a, a ∉ ["occ", "nj", "fj"] → σ3.arrs a = σ2.arrs a := fun a ha =>
    hfa3 a (by simp [bucketLoop, bucketBody, Com.warrs] at ha ⊢; tauto)
  have hP3 : σ3.vars "P" = P := by rw [hfv3' "P" (by decide)]; exact hP2
  -- block starts
  obtain ⟨σ4, hr4, ⟨ha4, hn4, hst4, hnx4⟩, hfv4, hfa4, -, ho4⟩ :=
    (startLoop_spec (B := B) (x := x) (n := n) (occ := occB x n) Lo P hxg hB2 hnB hxB hpB
      hnlex hjc hdueB hdueL (fun j hj => hs.occ_true hj)).frame σ3
      ⟨ha3, hn3, hP3, hocc3,
        by rw [run_arrs_length hr3 "occ", harr2 "occ" (by decide), harr1]; exact hfr.locc,
        by rw [harr3 "st" (by decide), harr2 "st" (by decide), harr1]; exact hfr.lst,
        by rw [harr3 "nx2" (by decide), harr2 "nx2" (by decide), harr1]; exact hfr.lnx2⟩
  have hfv4' : ∀ y, y ∉ ["Pm", "j", "dd", "ok", "nx", "e"] → σ4.vars y = σ3.vars y :=
    fun y hy => hfv4 y (by
      simp [startLoop, startBody, scanLoop, scanBody, Com.wvars] at hy ⊢; tauto)
  have harr4 : ∀ a, a ∉ ["st", "nx2"] → σ4.arrs a = σ3.arrs a := fun a ha =>
    hfa4 a (by simp [startLoop, startBody, scanLoop, scanBody, Com.warrs] at ha ⊢; tauto)
  -- the arrays the order pass reads
  have hsrc4 : Src x n P Lo σ4 := by
    refine ⟨ha4, hn4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d; rw [harr4 "fj" (by decide)]; exact hfj3 d
    · intro j hj; rw [harr4 "nj" (by decide)]; exact hnj3 j hj
    · intro d hd
      obtain ⟨j, hj, rfl⟩ := hs.occ_mem hd
      exact hst4 j hj
    · intro d hd
      obtain ⟨j, hj, rfl⟩ := hs.occ_mem hd
      exact hnx4 j hj
    · rw [harr4 "ord" (by decide), harr3 "ord" (by decide), harr2 "ord" (by decide), harr1]
      exact hfr.lord
    · rw [harr4 "dl" (by decide), harr3 "dl" (by decide), harr2 "dl" (by decide), harr1]
      exact hfr.ldl
    · rw [harr4 "nc" (by decide), harr3 "nc" (by decide), harr2 "nc" (by decide), harr1]
      exact hfr.lnc
    · rw [harr4 "nj" (by decide)]; exact hnjL3
    · rw [harr4 "fj" (by decide), run_arrs_length hr3 "fj", harr2 "fj" (by decide), harr1]
      exact hfr.lfj
    · rw [run_arrs_length hr4 "st", harr3 "st" (by decide), harr2 "st" (by decide), harr1]
      exact hfr.lst
    · rw [run_arrs_length hr4 "nx2", harr3 "nx2" (by decide), harr2 "nx2" (by decide), harr1]
      exact hfr.lnx2
  -- walk the blocks
  obtain ⟨σ5, K5, hr5, hsrc5, hhp5, hoin5, hK5⟩ :=
    orderLoop_run (B := B) (x := x) (n := n) (P := P) (M := Lo) (Lo := Lo)
      (fun e he => by have := hs.occ_mxE he; omega) hs.occ0 hnB
      (fun d hd => by have := hs.occ_mxE hd; omega)
      (fun d hd => by have := hs.occ_mxE hd; omega) hjc hnlex hxB hs.pPos σ4 hsrc4
  have hfv5 : ∀ y, y ∉ ["kk", "hp", "dd", "cur", "nc0", "ib", "jp"] →
      σ5.vars y = σ4.vars y := fun y hy =>
    hr5.frame_var y (by
      simp [orderLoop, orderBody, openStep, blockLoop, walkBody, emitLoop, emitStep,
        Com.wvars] at hy ⊢
      tauto)
  have harr5 : ∀ a, a ∉ ["ord", "dl", "nc"] → σ5.arrs a = σ4.arrs a := fun a ha =>
    hr5.frame_arr a (by
      simp [orderLoop, orderBody, openStep, blockLoop, walkBody, emitLoop, emitStep,
        Com.warrs] at ha ⊢
      tauto)
  obtain ⟨hkk5, ordF, dlF, ncF, hOrd, hordA, hdlA, hncA⟩ :=
    order_final (x := x) (n := n) (P := P) (M := Lo) (I := I) (σ := σ5) rfl hs.npos
      (fun j => hs.enc.due_eq j) (fun j => hs.pjP j)
      (fun e he => by have := hs.occ_mxE he; omega) hs.occ0 hoin5
  -- the context the sweep runs in
  have hvchain : ∀ y, y ∉ ["kk", "hp", "dd", "cur", "nc0", "ib", "jp"] →
      y ∉ ["Pm", "j", "ok", "nx", "e"] → y ∉ ["S", "i"] → y ∉ ["P", "v"] →
      σ5.vars y = σ.vars y := by
    intro y h1 h2 h3 h4
    rw [hfv5 y h1, hfv4' y (by simp at h1 h2 ⊢; tauto), hfv3' y (by simp at h1 h2 ⊢; tauto),
      hfv2' y h3, hfv1 y (by simp [pmaxLoop, pmaxBody, Com.wvars] at h2 h4 ⊢; tauto)]
  have harrchain : ∀ a, a ∉ ["ord", "dl", "nc"] → a ∉ ["st", "nx2"] →
      a ∉ ["occ", "nj", "fj"] → a ≠ "pw" → σ5.arrs a = σ.arrs a := by
    intro a h1 h2 h3 h4
    rw [harr5 a h1, harr4 a h2, harr3 a h3, harr2 a h4, harr1 a]
  have hSv5 : σ5.vars "S" = S := by
    rw [hfv5 "S" (by decide), hfv4' "S" (by decide), hfv3' "S" (by decide)]; exact hS2
  have hPv5 : σ5.vars "P" = P := by
    rw [hfv5 "P" (by decide), hfv4' "P" (by decide)]; exact hP3
  have hpw5 : Pw m P σ5 := by
    rw [Pw, harr5 "pw" (by decide), harr4 "pw" (by decide), harr3 "pw" (by decide)]
    exact hpw2
  have hctx5 : Ctx I P n S W ordF dlF ncF x σ5 := by
    refine ⟨hsrc5.arrA, hsrc5.varn, ?_, hPv5, hSv5, ?_, ?_, ?_, hpw5, hordA, hdlA, hncA,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hvchain "m" (by decide) (by decide) (by decide) (by decide)]; exact hmv
    · rw [hvchain "cap" (by decide) (by decide) (by decide) (by decide)]; exact hcapv
    · rw [hvchain "O0" (by decide) (by decide) (by decide) (by decide)]; exact hO0v
    · rw [hvchain "T0" (by decide) (by decide) (by decide) (by decide)]; exact hT0v
    · rw [harrchain "V" (by decide) (by decide) (by decide) (by decide)]; exact hfr.lV
    · rw [harrchain "V2" (by decide) (by decide) (by decide) (by decide)]; exact hfr.lV2
    · rw [harrchain "Vt" (by decide) (by decide) (by decide) (by decide)]; exact hfr.lVt
    · rw [run_arrs_length hr5 "ord"]; exact hsrc4.lord
    · rw [run_arrs_length hr5 "dl"]; exact hsrc4.ldl
    · rw [run_arrs_length hr5 "nc"]; exact hsrc4.lnc
  -- the bounds the sweep runs under
  have hWmx : W ≤ mxE x := by rw [← hs.wv]; exact getD_le_mxE x _
  have hBnd : Bnd B I P n S W dlF x := by
    refine ⟨rfl, hsB, hmB, hpB, by omega, hxg, hxB, hnB, ?_, fun i => ?_⟩
    · intro k hk
      have h1 : dlF k = I.d (ordF k) := hOrd.dl_eq k hk
      have h2 : due x (ordF k).val = I.d (ordF k) := hs.enc.due_eq (ordF k)
      have h3 := hs.dueMx (ordF k).val
      omega
    · have := getD_le_mxE x i; omega
  -- the sweep
  obtain ⟨σ6, hr6, ⟨hctx6, hkn6, htp6, hacc6, T6, hTV6, hTab6⟩, hk6⟩ :=
    sweepLoop_spec (B := B) hOrd hBnd hs.enc ⟨0, hs.mpos⟩ σ5 hctx5
  rw [hk6] at hacc6 hTab6
  -- close the last block
  obtain ⟨σ7, hr7, ⟨⟨bst, hub, hat, hacc7⟩, hTV7, hS7, hcap7, hacc7le⟩, hfv7, hfa7, -, ho7⟩ :=
    (closeBlock_spec (B := B) S W T6 hsB (fun c _ => hTab6.cap c) hBnd.cB).frame σ6
      ⟨hctx6.varS, hTV6, hctx6.varcap, by rw [hacc6]; exact min_le_right _ _⟩
  have hbst : bst = min (optimumOn I (seg ordF (cut ncF n) n).toFinset) W + 1 := by
    refine SweepDP.tab_best (I := I) (P := P) hOrd.pmax hTab6
      (seg_ord hOrd (le_refl n) (cut_le ncF n) (fun j h1 h2 => cut_gap ncF n j h1 h2))
      (seg_nodup hOrd (le_refl n)) (fun c hc => hub c hc) ?_
    rcases hat with h0 | ⟨c, hc, hTc⟩
    · exact Or.inl h0
    · exact Or.inr ⟨c, hc, hTc⟩
  have hacc7' : σ7.vars "acc" = min (optimum I) W := by
    rw [hacc7, hacc6, hbst, ← optimumOn_full hOrd, optimumOn_split' hOrd (le_refl n)]
    exact min_add_min _ _ _
  -- the output tape is still empty
  have hout7 : σ7.out = [] := by
    rw [hr7.out_eq (by simp [closeBlock, bestLoop, bestBody, Com.NoWrite]),
      hr6.out_eq (by simp [sweepLoop, sweepBody, startJob, jobData, entryLoop, entryBody,
        takeLoop, takeBody, closeBlock, bestLoop, bestBody, clearLoop, zeroLoopOf,
        zeroBodyOf, commitLoop, shiftLoop, zeroLoop, shiftBody, advLoop, advBody,
        commitBody, relaxLoop, relaxBody, Com.NoWrite]),
      hr5.out_eq (by simp [orderLoop, orderBody, openStep, blockLoop, walkBody, emitLoop,
        emitStep, Com.NoWrite]),
      hr4.out_eq (by simp [startLoop, startBody, scanLoop, scanBody, Com.NoWrite]),
      hr3.out_eq (by simp [bucketLoop, bucketBody, Com.NoWrite]),
      hr2.out_eq (by simp [powLoop, powBody, Com.NoWrite]),
      hr1.out_eq (by simp [pmaxLoop, pmaxBody, Com.NoWrite])]
    exact houtx
  -- the answer
  have hWB := hs.wB
  have hcv : (Cond.lt (V "acc") (V "cap")).evalB B σ7
      = some (decide (σ7.vars "acc" < σ7.vars "cap")) := by
    simp [Cond.evalB, Expr.evalB, fit_self (show σ7.vars "acc" < B by
      rw [hacc7']; have := min_le_right (optimum I) W; omega),
      fit_self (show σ7.vars "cap" < B by rw [hcap7]; omega)]
  have hans : ∃ σ8, Run B (.ite (.lt (V "acc") (V "cap")) (.write (lit 0)) (.write (lit 1)))
      σ7 σ8 6 ∧ σ8.out = [if W ≤ optimum I then 1 else 0] := by
    by_cases hlt : σ7.vars "acc" < σ7.vars "cap"
    · refine ⟨_, (Run.ite_true (K := 2) (by rw [hcv, decide_eq_true hlt])
        ((Run.write (ReadHdr.evalB_lit (show (0 : ℕ) < B by omega))).mono
          (by norm_num [Expr.size]))).mono (by norm_num [Cond.size, Expr.size]), ?_⟩
      rw [hacc7', hcap7] at hlt
      have : ¬ (W ≤ optimum I) := by have := min_le_left (optimum I) W; omega
      simp only [hout7, if_neg this]
      rfl
    · refine ⟨_, (Run.ite_false (K := 2) (by
        rw [hcv, decide_eq_false hlt])
        ((Run.write (ReadHdr.evalB_lit (show (1 : ℕ) < B by omega))).mono
          (by norm_num [Expr.size]))).mono (by norm_num [Cond.size, Expr.size]), ?_⟩
      rw [hacc7', hcap7] at hlt
      have : W ≤ optimum I := by
        have h1 := min_le_left (optimum I) W
        have h2 := min_le_right (optimum I) W
        omega
      simp only [hout7, if_pos this]
      rfl
  obtain ⟨σ8, hr8, hout8⟩ := hans
  -- the cost
  have hsum : (∑ j ∈ Finset.range n, bodyCost m S (elenOf x (ordF j).val))
      = n * ((44 * m + 148) * S + 117) + (84 * S + 24) * offset x I.jobs :=
    sum_bodyCost _ _ _ _ _ (sum_elen_ord hOrd hs.enc)
  have hxlen' : x.length = 3 + 4 * n + offset x I.jobs + 1 := by
    rw [hndef]; exact hs.xlen
  have hSpos : 0 < S := by rw [hSdef]; exact Nat.pow_pos (by omega)
  have hPS : P < S := by rw [hSdef]; exact lt_pow_self hs.mpos
  have hbd : ∀ a b c : ℕ, a ≤ S → b ≤ m + 1 → c ≤ x.length + 1 →
      a * (b * c) ≤ S * ((m + 1) * (x.length + 1)) :=
    fun a b c ha hb hc => Nat.mul_le_mul ha (Nat.mul_le_mul hb hc)
  have r1 : n * (m * S) ≤ S * ((m + 1) * (x.length + 1)) := by
    have h := hbd S m n (le_refl S) (by omega) (by omega)
    calc n * (m * S) = S * (m * n) := by ring
      _ ≤ _ := h
  have r2 : n * S ≤ S * ((m + 1) * (x.length + 1)) := by
    have h := hbd S 1 n (le_refl S) (by omega) (by omega)
    calc n * S = S * (1 * n) := by ring
      _ ≤ _ := h
  have r3 : offset x I.jobs * S ≤ S * ((m + 1) * (x.length + 1)) := by
    have h := hbd S 1 (offset x I.jobs) (le_refl S) (by omega) (by omega)
    calc offset x I.jobs * S = S * (1 * offset x I.jobs) := by ring
      _ ≤ _ := h
  have r4 : P * n ≤ S * ((m + 1) * (x.length + 1)) := by
    have h := hbd P 1 n (by omega) (by omega) (by omega)
    calc P * n = P * (1 * n) := by ring
      _ ≤ _ := h
  have r5 : S ≤ S * ((m + 1) * (x.length + 1)) := by
    have h := hbd S 1 1 (le_refl S) (by omega) (by omega); simpa using h
  have r6 : x.length + 1 ≤ S * ((m + 1) * (x.length + 1)) := by
    have h := hbd 1 1 (x.length + 1) (by omega) (by omega) (le_refl _); simpa using h
  have r7 : m + 1 ≤ S * ((m + 1) * (x.length + 1)) := by
    have h := hbd 1 (m + 1) 1 (by omega) (le_refl _) (by omega); simpa using h
  refine ⟨σ8, (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 (Run.seq hr5
    (Run.seq hr6 (Run.seq hr7 hr8))))))).mono ?_, hout8⟩
  rw [hsum]
  have e1 : (43 * (P - 1) + 31) * n ≤ 43 * (P * n) + 31 * n := by
    calc (43 * (P - 1) + 31) * n ≤ (43 * P + 31) * n :=
          Nat.mul_le_mul_right n (by omega)
      _ = 43 * (P * n) + 31 * n := by ring
  have e2 : n * ((44 * m + 148) * S + 117) = 44 * (n * (m * S)) + 148 * (n * S) + 117 * n := by
    ring
  have e3 : (84 * S + 24) * offset x I.jobs
      = 84 * (offset x I.jobs * S) + 24 * offset x I.jobs := by ring
  omega

/-! ### The Degenerate Cases -/

lemma optimum_eq_zero_of_machines {I : Instance} (h : I.machines = 0) : optimum I = 0 := by
  refine Nat.le_antisymm (Finset.sup_le fun σ hσ => ?_) (Nat.zero_le _)
  have hf := (Finset.mem_filter.mp hσ).2
  have hnone : ∀ j, σ j = none := by
    intro j
    rcases hj : σ j with _ | i
    · rfl
    · exact absurd i.isLt (by omega)
  simp only [Instance.weight]
  rw [Finset.sum_eq_zero fun j _ => by rw [hnone j]; rfl]

lemma optimum_eq_zero_of_jobs {I : Instance} (h : I.jobs = 0) : optimum I = 0 := by
  refine Nat.le_antisymm (Finset.sup_le fun σ _ => ?_) (Nat.zero_le _)
  simp only [Instance.weight]
  rw [Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)]

/-! ### The Whole Program -/

set_option maxHeartbeats 1000000 in
theorem com_spec {I : Instance} {W : ℕ} (hdec : EncodesDecisionInstance x I W)
    (hbig : 4 * ((pmaxOf x + 1) ^ I.machines + 2 * mxE x + x.length) + 64 ≤ B)
    (hlo : B ≤ Lo) :
    Spec B (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "a").length = x.length ∧
        Fresh I.jobs I.machines ((pmaxOf x + 1) ^ I.machines) Lo σ)
      com
      (fun _ σ' => σ'.out = [if W ≤ optimum I then 1 else 0])
      (1200 * ((pmaxOf x + 1) ^ I.machines * ((I.machines + 1) * (x.length + 1)))) := by
  classical
  obtain ⟨hEn, hxlen, hmc, hWv⟩ := enc_of_decision hdec
  have hmxB : mxE x + 2 < B := by omega
  have hxB : x.length + 2 < B := by omega
  have hy : ∀ v ∈ x, v < B := fun v hv => by
    have := Lax470956Proofs.Pmax.le_foldr_max hv; simp only [mxE] at hmxB; omega
  have hQpos : 0 < (pmaxOf x + 1) ^ I.machines := Nat.pow_pos (by omega)
  have hQR : x.length + 1 ≤
      (pmaxOf x + 1) ^ I.machines * ((I.machines + 1) * (x.length + 1)) := by
    have : 1 * (1 * (x.length + 1)) ≤
        (pmaxOf x + 1) ^ I.machines * ((I.machines + 1) * (x.length + 1)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (le_refl _))
    simpa using this
  intro σ ⟨hinp, hout, halen, hfr⟩
  -- read the word
  obtain ⟨σ1, hr1, ⟨ha1, hout1, hinp1, hL1, -⟩, hfv1, hfa1, -, -⟩ :=
    (readWord_spec (B := B) (y := x) I.jobs (offset x I.jobs) hy (by omega) hEn.jc
      (by rw [offset, hEn.jc]; congr 1; omega) hxlen).frame σ ⟨hinp, hout, halen⟩
  have harr1 : ∀ a, a ≠ "a" → σ1.arrs a = σ.arrs a := fun a ha =>
    hfa1 a (by
      simp [ReadHdr.readWord, ReadHdr.readUpTo, Lax470956Proofs.ReadAll.readBody,
        Com.warrs]
      exact ha)
  -- the header
  obtain ⟨σ2, hr2, ⟨hn2, hm2, hW2, hcap2, hO02, hT02⟩, hfv2, hfa2, -, ho2⟩ :=
    (header_spec (B := B) (x := x) I.jobs I.machines W (fun i => by
        have := getD_le_mxE x i; omega) hxB (by omega)
      (by rw [← hEn.jc]; rfl) (by rw [← hmc]; rfl) hWv).frame σ1 ⟨ha1, hL1⟩
  have harr2 : ∀ a, σ2.arrs a = σ1.arrs a := fun a =>
    hfa2 a (by simp [header, Com.warrs])
  have ha2 : σ2.arrs "a" = x := by rw [harr2, ha1]
  have hout2 : σ2.out = [] := by rw [ho2 (by simp [header, Com.NoWrite]), hout1]
  have hfr2 : Fresh I.jobs I.machines ((pmaxOf x + 1) ^ I.machines) Lo σ2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [harr2, harr1 _ (by decide)]
    exacts [hfr.lpw, hfr.locc, hfr.lfj, hfr.lst, hfr.lnx2, hfr.lnj, hfr.lord, hfr.ldl,
      hfr.lnc, hfr.lV, hfr.lV2, hfr.lVt, hfr.zocc, hfr.zfj]
  have hWlt : W < B := by have := getD_le_mxE x (x.length - 1); rw [hWv] at this; omega
  have hmM : I.machines ≤ mxE x := by rw [← hmc]; exact getD_le_mxE x 1
  have hnM : I.jobs ≤ mxE x := by rw [← hEn.jc]; exact getD_le_mxE x 0
  have hevW : (Cond.eq (V "W") (lit 0)).evalB B σ2 = some (σ2.vars "W" == 0) :=
    evalB_eqlit (by rw [hW2]; omega) (by omega)
  have hevm : (Cond.eq (V "m") (lit 0)).evalB B σ2 = some (σ2.vars "m" == 0) :=
    evalB_eqlit (by rw [hm2]; omega) (by omega)
  have hevn : (Cond.eq (V "n") (lit 0)).evalB B σ2 = some (σ2.vars "n" == 0) :=
    evalB_eqlit (by rw [hn2]; omega) (by omega)
  -- the degenerate answer
  have hdeg : optimum I = 0 → ∃ σ3, Run B (.ite (.eq (V "W") (lit 0))
      (.write (lit 1)) (.write (lit 0))) σ2 σ3 6 ∧
      σ3.out = [if W ≤ optimum I then 1 else 0] := by
    intro hopt
    by_cases hW0 : W = 0
    · refine ⟨_, (Run.ite_true (K := 2) (by rw [hevW, hW2, hW0]; rfl)
        ((Run.write (ReadHdr.evalB_lit (show (1 : ℕ) < B by omega))).mono
          (by norm_num [Expr.size]))).mono (by norm_num [Cond.size, Expr.size]), ?_⟩
      simp only [hout2, hopt, if_pos (by omega : W ≤ 0)]
      rfl
    · refine ⟨_, (Run.ite_false (K := 2) (by
        rw [hevW, hW2]; simp [hW0])
        ((Run.write (ReadHdr.evalB_lit (show (0 : ℕ) < B by omega))).mono
          (by norm_num [Expr.size]))).mono (by norm_num [Cond.size, Expr.size]), ?_⟩
      simp only [hout2, hopt, if_neg (by omega : ¬ (W ≤ 0))]
      rfl
  by_cases hm0 : I.machines = 0
  · obtain ⟨σ3, hr3, hout3⟩ := hdeg (optimum_eq_zero_of_machines hm0)
    exact ⟨σ3, (Run.seq hr1 (Run.seq hr2 (Run.ite_true (K := 6)
      (by rw [hevm, hm2, hm0]; rfl) hr3))).mono (by
        simp only [Cond.size, Expr.size]; omega), hout3⟩
  · by_cases hn0 : I.jobs = 0
    · obtain ⟨σ3, hr3, hout3⟩ := hdeg (optimum_eq_zero_of_jobs hn0)
      exact ⟨σ3, (Run.seq hr1 (Run.seq hr2 (Run.ite_false (K := 10)
        (by rw [hevm, hm2]; simp [hm0])
        (Run.ite_true (K := 6) (by rw [hevn, hn2, hn0]; rfl) hr3)))).mono (by
          simp only [Cond.size, Expr.size]; omega), hout3⟩
    · have hsz : Sizes B x I W Lo := ⟨hdec, by omega, by omega, hbig, hlo⟩
      obtain ⟨σ3, hr3, hout3⟩ := mainWork_spec hsz σ2
        ⟨hfr2, ha2, hout2, hn2, hm2, hW2, hcap2, hO02, hT02⟩
      refine ⟨σ3, (Run.seq hr1 (Run.seq hr2 (Run.ite_false (K := _)
        (by rw [hevm, hm2]; simp [hm0])
        (Run.ite_false (K := _) (by rw [hevn, hn2]; simp [hn0]) hr3)))).mono ?_, hout3⟩
      simp only [Cond.size, Expr.size]
      omega

/-! ### The Machine Program -/

/-- The value bound the program runs under. -/
def Bof (x : List ℕ) : ℕ :=
  4 * ((pmaxOf x + 1) ^ machineCount x + 2 * mxE x + x.length) + 64

/-- The array lengths. -/
def extOf (x : List ℕ) : String → ℕ := fun a =>
  if a = "a" then x.length
  else if a = "pw" then machineCount x
  else if a = "occ" ∨ a = "fj" ∨ a = "st" ∨ a = "nx2" then Bof x
  else if a = "nj" ∨ a = "ord" ∨ a = "dl" ∨ a = "nc" then jobCount x
  else (pmaxOf x + 1) ^ machineCount x

/-- The cost, in IMP+ units. -/
def Kof (x : List ℕ) : ℕ :=
  1200 * ((pmaxOf x + 1) ^ machineCount x * ((machineCount x + 1) * (x.length + 1)))

lemma S_le_Q (x : List ℕ) :
    (pmaxOf x + 1) ^ machineCount x
      ≤ (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) := by
  rcases Nat.eq_zero_or_pos (machineCount x) with h | h
  · rw [h]; simp
  · calc (pmaxOf x + 1) ^ machineCount x
        ≤ (machineCount x * pmaxOf x + 1) ^ machineCount x :=
          Nat.pow_le_pow_left (by
            have : pmaxOf x ≤ machineCount x * pmaxOf x := Nat.le_mul_of_pos_left _ h
            omega) _
      _ ≤ (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) :=
          Nat.pow_le_pow_right (by omega) (by omega)

lemma fits_max {c w : ℕ} {y : List ℕ} (hne : y ≠ []) (h : Fits c w y) :
    c * (y.length + mxE y + 1) ≤ 2 ^ w := by
  rcases Lax470956Proofs.Pmax.foldr_max_mem_or_zero y with hm | hm
  · exact h _ hm
  · rw [mxE, hm]
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact le_trans (Nat.mul_le_mul_left c (by omega)) (h a (by simp))

open Classical in
/-- The admissible words at word length `w`. -/
def Dom (w : ℕ) : Set (List ℕ) :=
  {x | x ∈ DecisionInstances ∧ Fits 12001 w x ∧
    12001 * (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) ≤ 2 ^ w}

open Classical in
theorem solves (w : ℕ) :
    Solves layout com (Dom w)
      (fun x => if byMachinesAndPmax.Yes x then [1] else [0]) Bof Kof where
  ok := com_ok
  inp := by
    intro x _ v hv
    have := Lax470956Proofs.Pmax.le_foldr_max hv
    simp only [Bof, mxE] at *
    omega
  run := by
    intro x hx
    obtain ⟨I, W, hdec⟩ := hx.1
    obtain ⟨hEn, hxlen, hmc, hWv⟩ := enc_of_decision hdec
    have hbig : 4 * ((pmaxOf x + 1) ^ I.machines + 2 * mxE x + x.length) + 64 ≤ Bof x := by
      rw [Bof, hmc]
    have hfresh : Fresh I.jobs I.machines ((pmaxOf x + 1) ^ I.machines) (Bof x)
        (initEnv (extOf x) x) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [initEnv, extOf, List.length_replicate, hmc, hEn.jc] <;>
        first
          | rfl
          | (intro d; rw [List.getD_eq_getElem?_getD]
             rcases h : (List.replicate (Bof x) (0 : ℕ))[d]? with _ | v
             · rfl
             · have := List.getElem?_eq_some_iff.mp h
               obtain ⟨hd, hv⟩ := this
               rw [← hv, List.getElem_replicate])
          | simp
    obtain ⟨σ', hrun, hout⟩ :=
      com_spec (B := Bof x) (Lo := Bof x) hdec hbig (le_refl _) (initEnv (extOf x) x)
        ⟨rfl, rfl, by simp [initEnv, extOf], hfresh⟩
    refine ⟨extOf x, σ', hrun.mono ?_, ?_⟩
    · rw [Kof, hmc]
    · rw [hout]
      have hyes : byMachinesAndPmax.Yes x ↔ W ≤ optimum I := by
        constructor
        · rintro ⟨I', W', hdec', hw'⟩
          obtain ⟨rfl, rfl⟩ := decision_unique hdec' hdec
          exact (hasWeight_iff I' W').mp hw'
        · intro h
          exact ⟨I, W, hdec, (hasWeight_iff I W).mpr h⟩
      by_cases hc : W ≤ optimum I
      · rw [if_pos hc, if_pos (hyes.mpr hc)]
      · rw [if_neg hc, if_neg (fun h => hc (hyes.mp h))]

def prog : Program := compileProgram layout com

set_option maxRecDepth 8000 in
open Classical in
theorem prog_computesInTime (w : ℕ) :
    ComputesInTime w prog (Dom w)
      (fun x => if byMachinesAndPmax.Yes x then [1] else [0])
      (fun x => 12001 * (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) *
        (machineCount x + 1) * (x.length + 1)) := by
  refine computesInTime_of_solves (solves w) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨⟨I, W, hdec⟩, hfits, htab⟩ := hx
    have hne : x ≠ [] := by obtain ⟨y, rfl, -⟩ := hdec; simp
    have h1 := fits_max hne hfits
    have h2 : 12001 * (pmaxOf x + 1) ^ machineCount x ≤ 2 ^ w :=
      le_trans (Nat.mul_le_mul_left _ (S_le_Q x)) htab
    refine fitsWords_of_max_le (by simp only [Bof]; omega) ?_
    simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff, Bof]
    constructor <;> omega
  · obtain ⟨-, -, htab⟩ := hx
    have hSQ := S_le_Q x
    have hQpos : 0 < (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) :=
      Nat.pow_pos (by omega)
    have hYZ : (pmaxOf x + 1) ^ machineCount x * ((machineCount x + 1) * (x.length + 1))
        ≤ (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) * (machineCount x + 1)
          * (x.length + 1) := by
      calc (pmaxOf x + 1) ^ machineCount x * ((machineCount x + 1) * (x.length + 1))
          ≤ (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) *
              ((machineCount x + 1) * (x.length + 1)) := Nat.mul_le_mul_right _ hSQ
        _ = _ := by ring
    have hZpos : 1 ≤ (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) *
        (machineCount x + 1) * (x.length + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hT : 12001 * (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) *
        (machineCount x + 1) * (x.length + 1)
        = 12001 * ((machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) *
          (machineCount x + 1) * (x.length + 1)) := by ring
    rw [const_eq, hT]
    simp only [Kof]
    omega

open Classical in
/-- **Theorem 3's program**: one word RAM program and one constant decide the problem
within the stated bound, at every word length that admits the instance and its table. -/
theorem fptTime :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧
          c * (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) ≤ 2 ^ w}
        (fun x => if byMachinesAndPmax.Yes x then [1] else [0])
        (fun x => c * (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) *
          (machineCount x + 1) * (x.length + 1)) :=
  ⟨prog, 12001, fun w => prog_computesInTime w⟩

end Lax470956Proofs.SweepMain
