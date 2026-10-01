import Lax470956Proofs.SweepMain
import Lax470956Proofs.Brute
import Lax470956Proofs.BruteProg

/-!
The brute force, one string at a time: what a pass over the word and the string computes.
-/

namespace Lax470956Proofs.BruteEval

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.Scheduling Lax470956.Scheduling.Instance
open Lax470956.InstanceEncoding
open Lax470956Proofs.SweepProg Lax470956Proofs.BruteProg Lax470956Proofs.SweepBody

variable {B : ℕ} {x : List ℕ}

/-! ### Eligibility -/

lemma exists_lt_succ {P : ℕ → Prop} {e : ℕ} :
    (∃ r, r < e + 1 ∧ P r) ↔ (∃ r, r < e ∧ P r) ∨ P e := by
  constructor
  · rintro ⟨r, hr, hp⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | rfl
    · exact Or.inl ⟨r, h, hp⟩
    · exact Or.inr hp
  · rintro (⟨r, hr, hp⟩ | hp)
    · exact ⟨r, by omega, hp⟩
    · exact ⟨e, by omega, hp⟩

/-- The state of the scan over the targets of one job. -/
def EInv (x : List ℕ) (n o1 v elen : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "T0" = 3 + 4 * n ∧ σ.vars "o1" = o1 ∧ σ.vars "va" = v ∧
    σ.vars "elen" = elen ∧ σ.vars "e" ≤ elen ∧ σ.vars "fnd" ≤ 1 ∧
    (σ.vars "fnd" = 1 ↔ ∃ r, r < σ.vars "e" ∧ x.getD (3 + 4 * n + (o1 + r)) 0 + 1 = v)

theorem eligStep_spec (n o1 v elen : ℕ) (hxg : ∀ i, x.getD i 0 + 2 < B)
    (hT : 3 + 4 * n + (o1 + elen) + 2 < B) (hv : v + 2 < B) (he : elen + 2 < B)
    (hlen : 3 + 4 * n + (o1 + elen) ≤ x.length) :
    Spec B (fun σ => EInv x n o1 v elen σ ∧ σ.vars "e" < elen) eligStep
      (fun σ σ' => EInv x n o1 v elen σ' ∧ σ'.vars "e" = σ.vars "e" + 1) 40 := by
  run_vcg
  all_goals obtain ⟨ha, hT0, ho1', hva, helen, he', hf1, hfiff⟩ := ‹EInv x n o1 v elen σ›
  all_goals have hlt : σ.vars "e" < elen := ‹σ.vars "e" < elen›
  all_goals have haL : (σ.arrs "a").length = x.length := (by rw [ha])
  all_goals have hval : (σ.arrs "a").getD (σ.vars "T0" + (σ.vars "o1" + σ.vars "e")) 0
      = x.getD (3 + 4 * n + (o1 + σ.vars "e")) 0 := (by rw [ha, hT0, ho1'])
  all_goals have hxe := hxg (3 + 4 * n + (o1 + σ.vars "e"))
  all_goals try (rw [hval]; omega)
  all_goals try omega
  all_goals simp only [EInv, Env.setVar, String.reduceEq, ↓reduceIte]
  · refine ⟨⟨ha, hT0, ho1', hva, helen, by omega, by omega, ?_⟩, trivial⟩
    refine (true_iff _).mpr ?_
    rw [exists_lt_succ]
    exact Or.inr (by omega)
  · refine ⟨⟨ha, hT0, ho1', hva, helen, by omega, hf1, ?_⟩, trivial⟩
    rw [hfiff, exists_lt_succ]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exfalso; omega

/-- The whole scan of one job's block of targets. -/
theorem eligLoop_spec (n m Lb : ℕ) (hxg : ∀ i, x.getD i 0 + 2 < B)
    (hxB : x.length + 2 < B) (hmB : m + 2 < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "T0" = 3 + 4 * n ∧ σ.vars "va" ≤ m ∧
        3 + 4 * n + (σ.vars "o1" + σ.vars "elen") ≤ x.length ∧ σ.vars "elen" ≤ Lb)
      eligLoop
      (fun σ σ' => (∀ y, y ≠ "fnd" → y ≠ "e" → σ'.vars y = σ.vars y) ∧
        (∀ a, σ'.arrs a = σ.arrs a) ∧ σ'.vars "fnd" ≤ 1 ∧
        (σ'.vars "fnd" = 1 ↔ ∃ r, r < σ.vars "elen" ∧
          x.getD (3 + 4 * n + (σ.vars "o1" + r)) 0 + 1 = σ.vars "va"))
      (44 * Lb + 8) := by
  intro σ ⟨ha, hT0, hva, hlen, hL⟩
  have hgen := (Spec.forRangeZero (B := B) "e" "elen"
    (EInv x n (σ.vars "o1") (σ.vars "va") (σ.vars "elen")) (σ.vars "elen") 40
    (by have : σ.vars "elen" ≤ x.length := by omega
        omega)
    (fun _ h => h.2.2.2.2.2.1) (fun _ h => h.2.2.2.2.1)
    (eligStep_spec (B := B) (x := x) n (σ.vars "o1") (σ.vars "va") (σ.vars "elen") hxg
      (by omega) (by omega) (by omega) hlen))
  obtain ⟨σ', hrun, hI, he⟩ := hgen (σ.setVar "fnd" 0)
    ⟨by simp [Env.setVar, ha], by simp [Env.setVar, hT0], by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
  obtain ⟨ha', hT0', ho1', hva', helen', -, hf1, hfiff⟩ := hI
  have hr := (Run.seq (Run.assign (v := 0) (SweepBody.evalB_lit (by omega))) hrun).mono
    (show 2 + ((40 + 4) * σ.vars "elen" + 6) ≤ 44 * Lb + 8 by omega)
  refine ⟨σ', hr, fun y hy1 hy2 => ?_, fun a => ?_, hf1, ?_⟩
  · rw [hr.frame_var y (by simp [eligLoop, eligStep, Com.wvars]; tauto)]
  · exact hr.frame_arr a (by simp [eligLoop, eligStep, Com.warrs])
  · rw [hfiff, he]

/-! ### Digits and Machines -/

section Digits

variable {I : Instance}

lemma mach_zero : Brute.mach I 0 = none := by simp [Brute.mach]

lemma mach_pos {v : ℕ} (hv : v ≤ I.machines) (h0 : v ≠ 0) :
    Brute.mach I v = some ⟨v - 1, by omega⟩ := by
  rw [Brute.mach, dif_pos ⟨h0, by omega⟩]

lemma elim_mach {v : ℕ} (hv : v ≤ I.machines) (w : ℕ) :
    (Brute.mach I v).elim 0 (fun _ => w) = if v = 0 then 0 else w := by
  by_cases h0 : v = 0
  · subst h0; simp [mach_zero]
  · rw [mach_pos hv h0]; simp [h0]

/-- The digit of job `j` is legal exactly when it is `0` or names a machine in the job's
block of targets. -/
lemma mach_elig {x : List ℕ} (hEn : Enc I x) (j : Fin I.jobs) {v : ℕ} (hv : v ≤ I.machines) :
    (∀ i, Brute.mach I v = some i → i ∈ I.eligible j) ↔
      (v = 0 ∨ ∃ r, r < offset x (j.val + 1) - offset x j.val ∧
        x.getD (3 + 4 * I.jobs + (offset x j.val + r)) 0 + 1 = v) := by
  by_cases h0 : v = 0
  · subst h0; simp [mach_zero]
  · rw [mach_pos hv h0]
    have hnext : offset x (j.val + 1) ≤ offset x I.jobs :=
      hEn.off_mono' I.jobs (le_refl _) _ j.isLt
    have hmono := hEn.off_mono j.val j.isLt
    simp only [Option.some.injEq, forall_eq', h0, false_or]
    rw [hEn.eligible_iff j ⟨v - 1, by omega⟩]
    constructor
    · rintro ⟨t, h1, h2, h3⟩
      refine ⟨t - offset x j.val, by omega, ?_⟩
      have : t = offset x j.val + (t - offset x j.val) := by omega
      have h3' : target x t = v - 1 := h3
      rw [target, hEn.jc] at h3'
      rw [← this]; omega
    · rintro ⟨r, hr, h3⟩
      refine ⟨offset x j.val + r, by omega, by omega, ?_⟩
      show target x (offset x j.val + r) = v - 1
      rw [target, hEn.jc]; omega

end Digits

/-! ### The Context Every Pass Runs in -/

section Context

variable {I : Instance} {W : ℕ}

/-- What the word and the value bound say, in the shape the passes use. -/
structure Bd (B : ℕ) (x : List ℕ) (I : Instance) (W : ℕ) : Prop where
  dec : EncodesDecisionInstance x I W
  big : 4 * (2 * SweepMain.mxE x + x.length) + 64 ≤ B

namespace Bd

lemma enc (h : Bd B x I W) : Enc I x := (SweepMain.enc_of_decision h.dec).1
lemma xlen (h : Bd B x I W) : x.length = 3 + 4 * I.jobs + offset x I.jobs + 1 :=
  (SweepMain.enc_of_decision h.dec).2.1
lemma mc (h : Bd B x I W) : machineCount x = I.machines := (SweepMain.enc_of_decision h.dec).2.2.1
lemma wv (h : Bd B x I W) : x.getD (x.length - 1) 0 = W := (SweepMain.enc_of_decision h.dec).2.2.2
lemma xg (h : Bd B x I W) (i : ℕ) : x.getD i 0 + 2 < B := by
  have := SweepMain.getD_le_mxE x i; have := h.big; omega
lemma xx (h : Bd B x I W) (i j : ℕ) : x.getD i 0 + x.getD j 0 + 2 < B := by
  have := SweepMain.getD_le_mxE x i; have := SweepMain.getD_le_mxE x j; have := h.big; omega
lemma lenx (h : Bd B x I W) : x.length + 2 < B := by have := h.big; omega
lemma nB (h : Bd B x I W) : I.jobs + 2 < B := by
  have h1 : I.jobs = x.getD 0 0 := by rw [← h.enc.jc]; rfl
  have := h.xg 0; omega
lemma mB (h : Bd B x I W) : I.machines + 2 < B := by
  have h1 : I.machines = x.getD 1 0 := by rw [← h.mc]; rfl
  have := h.xg 1; omega
lemma wB (h : Bd B x I W) : W + 2 < B := by rw [← h.wv]; exact h.xg _
lemma nlen (h : Bd B x I W) : 3 + 4 * I.jobs ≤ x.length := by have := h.xlen; omega
lemma offle (h : Bd B x I W) : offset x I.jobs + 3 + 4 * I.jobs < x.length := by have := h.xlen; omega

end Bd

/-- The scalars and arrays no pass of the brute force changes, except the odometer's
digits. -/
structure Ctx (x : List ℕ) (I : Instance) (W : ℕ) (σ : Env) : Prop where
  ha : σ.arrs "a" = x
  hn : σ.vars "n" = I.jobs
  hm : σ.vars "m" = I.machines
  hW : σ.vars "W" = W
  hO0 : σ.vars "O0" = 2 + 3 * I.jobs
  hT0 : σ.vars "T0" = 3 + 4 * I.jobs
  hlen : (σ.arrs "asg").length = I.jobs
  hdig : ∀ i, (σ.arrs "asg").getD i 0 ≤ I.machines

/-- The digit of job `i`. -/
def dgOf (σ : Env) (i : ℕ) : ℕ := (σ.arrs "asg").getD i 0

/-- The schedule the digits read. -/
def schedD (I : Instance) (d : ℕ → ℕ) : I.Schedule := fun j => Brute.mach I (d j.val)

/-- The eligibility half of feasibility, for the jobs before `k`. -/
def ElUpTo (I : Instance) (d : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ j : Fin I.jobs, j.val < k → ∀ i, Brute.mach I (d j.val) = some i → i ∈ I.eligible j

/-- The state of the pass over the jobs. -/
def JInv (x : List ℕ) (I : Instance) (W : ℕ) (σ : Env) : Prop :=
  Ctx x I W σ ∧ σ.vars "j" ≤ I.jobs ∧ σ.vars "ok" ≤ 1 ∧ σ.vars "acc" ≤ W ∧
    (σ.vars "ok" = 1 ↔ ElUpTo I (dgOf σ) (σ.vars "j")) ∧
    σ.vars "acc" = Brute.wacc I (schedD I (dgOf σ)) W (σ.vars "j")

lemma ElUpTo_succ {d : ℕ → ℕ} {k : ℕ} (hk : k < I.jobs) :
    ElUpTo I d (k + 1) ↔ ElUpTo I d k ∧
      ∀ i, Brute.mach I (d k) = some i → i ∈ I.eligible ⟨k, hk⟩ := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact h1 j h
    · have : j = ⟨k, hk⟩ := Fin.ext h
      subst this; exact h2

lemma wacc_succ_of_lt (σ : I.Schedule) (W k : ℕ) (hk : k < I.jobs) :
    Brute.wacc I σ W (k + 1) =
      min (Brute.wacc I σ W k + (σ ⟨k, hk⟩).elim 0 (fun _ => I.w ⟨k, hk⟩)) W := by
  rw [Brute.wacc, dif_pos hk]

end Context

section JobStep

variable {I : Instance} {W : ℕ}

/-- Between two states, only the listed scalars moved, and no array. -/
def Only (X : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ X → σ'.vars y = σ.vars y) ∧ ∀ a, σ'.arrs a = σ.arrs a

lemma Ctx.only {σ σ' : Env} (h : Ctx x I W σ) {X : List String} (ho : Only X σ σ')
    (hX : ∀ y ∈ ["n", "m", "W", "O0", "T0"], y ∉ X) : Ctx x I W σ' := by
  have hv := fun y (hy : y ∈ ["n", "m", "W", "O0", "T0"]) => ho.1 y (hX y hy)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ho.2]; exact h.ha
  · rw [hv "n" (by simp)]; exact h.hn
  · rw [hv "m" (by simp)]; exact h.hm
  · rw [hv "W" (by simp)]; exact h.hW
  · rw [hv "O0" (by simp)]; exact h.hO0
  · rw [hv "T0" (by simp)]; exact h.hT0
  · rw [ho.2]; exact h.hlen
  · intro i; rw [ho.2]; exact h.hdig i

lemma offset_eq (hb : Bd B x I W) (k : ℕ) : offset x k = x.getD (2 + 3 * I.jobs + k) 0 := by
  rw [offset, hb.enc.jc]

lemma Bd.off_lt (hb : Bd B x I W) (k : ℕ) : offset x k + 2 < B := by
  rw [offset_eq hb]; exact hb.xg _

theorem jobFetch_spec (hb : Bd B x I W) :
    Spec B (fun σ => Ctx x I W σ ∧ σ.vars "j" < I.jobs) jobFetch
      (fun σ σ' => Only ["va", "o1", "o2", "elen"] σ σ' ∧
        σ'.vars "va" = dgOf σ (σ.vars "j") ∧ σ'.vars "o1" = offset x (σ.vars "j") ∧
        σ'.vars "elen" = offset x (σ.vars "j" + 1) - offset x (σ.vars "j")) 30 := by
  run_vcg
  all_goals obtain ⟨ha, hn, hm, hW', hO0, hT0, hlen, hdig⟩ := ‹Ctx x I W σ›
  all_goals have hj : σ.vars "j" < I.jobs := ‹σ.vars "j" < I.jobs›
  all_goals have haL : (σ.arrs "a").length = x.length := (by rw [ha])
  all_goals have hnl := hb.nlen
  all_goals have hoff1 : (σ.arrs "a").getD (σ.vars "O0" + σ.vars "j") 0
      = offset x (σ.vars "j") := (by rw [ha, hO0, offset_eq hb])
  all_goals have hoff2 : (σ.arrs "a").getD (σ.vars "O0" + σ.vars "j" + 1) 0
      = offset x (σ.vars "j" + 1) := (by rw [ha, hO0, offset_eq hb]; rfl)
  all_goals have hx1 := hb.xg (2 + 3 * I.jobs + σ.vars "j")
  all_goals have hx2 := hb.xg (2 + 3 * I.jobs + (σ.vars "j" + 1))
  all_goals have hd := hdig (σ.vars "j")
  all_goals have hmB := hb.mB
  all_goals have hnB := hb.nB
  all_goals have hlx := hb.lenx
  all_goals have ho1 := hb.off_lt (σ.vars "j")
  all_goals have ho2 := hb.off_lt (σ.vars "j" + 1)
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try rw [hoff1]
  all_goals try rw [hoff2]
  all_goals try omega
  refine ⟨⟨fun y hy => ?_, fun a => rfl⟩, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h1, h2, h3, h4⟩ := hy
  simp [h1, h2, h3, h4]
theorem jobFold_spec (hb : Bd B x I W) :
    Spec B (fun σ => Ctx x I W σ ∧ σ.vars "j" < I.jobs ∧ σ.vars "ok" ≤ 1 ∧
        σ.vars "acc" ≤ W ∧ σ.vars "va" ≤ I.machines ∧ σ.vars "fnd" ≤ 1) jobFold
      (fun σ σ' => Only ["ok", "acc", "j"] σ σ' ∧ σ'.vars "j" = σ.vars "j" + 1 ∧
        (σ'.vars "ok" = 1 ↔ σ.vars "ok" = 1 ∧ (σ.vars "va" = 0 ∨ σ.vars "fnd" = 1)) ∧
        σ'.vars "ok" ≤ 1 ∧
        σ'.vars "acc" = min (σ.vars "acc" +
          (if σ.vars "va" = 0 then 0 else wt x (σ.vars "j"))) W) 90 := by
  run_vcg
  all_goals obtain ⟨ha, hn, hm, hW', hO0, hT0, hlen, hdig⟩ := ‹Ctx x I W σ›
  all_goals have hj : σ.vars "j" < I.jobs := ‹σ.vars "j" < I.jobs›
  all_goals have hok : σ.vars "ok" ≤ 1 := ‹σ.vars "ok" ≤ 1›
  all_goals have hacc : σ.vars "acc" ≤ W := ‹σ.vars "acc" ≤ W›
  all_goals have hva : σ.vars "va" ≤ I.machines := ‹σ.vars "va" ≤ I.machines›
  all_goals have hfnd : σ.vars "fnd" ≤ 1 := ‹σ.vars "fnd" ≤ 1›
  all_goals have haL : (σ.arrs "a").length = x.length := (by rw [ha])
  all_goals have hnl := hb.nlen
  all_goals have hlx := hb.lenx
  all_goals have hwv : (σ.arrs "a").getD (2 + 2 * σ.vars "n" + σ.vars "j") 0 = wt x (σ.vars "j") := (by rw [ha, hn, wt, hb.enc.jc])
  all_goals have hwx : wt x (σ.vars "j") = x.getD (2 + 2 * I.jobs + σ.vars "j") 0 := (by rw [wt, hb.enc.jc])
  all_goals have hw1 := hb.xx (x.length - 1) (2 + 2 * I.jobs + σ.vars "j")
  all_goals have hWx := hb.wv
  all_goals have hmB := hb.mB
  all_goals have hWB := hb.wB
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try (rw [hwv]; omega)
  all_goals try omega
  all_goals simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals refine ⟨⟨fun y hy => ?_, fun a => rfl⟩, trivial, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3⟩ := hy; simp [h1, h2, h3]
  · omega
  · omega
  · rw [hwv, if_neg (by omega)]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3⟩ := hy; simp [h1, h2, h3]
  · omega
  · omega
  · rw [if_pos (by omega)]; omega

lemma Only.of_ne {X : List String} {σ σ' : Env} {a b : String}
    (h : (∀ y, y ≠ a → y ≠ b → σ'.vars y = σ.vars y) ∧ ∀ c, σ'.arrs c = σ.arrs c)
    (hX : X = [a, b]) : Only X σ σ' := by
  subst hX
  exact ⟨fun y hy => h.1 y (fun e => hy (by simp [e])) (fun e => hy (by simp [e])), h.2⟩

lemma dgOf_congr {σ σ' : Env} (h : σ'.arrs "asg" = σ.arrs "asg") : dgOf σ' = dgOf σ := by
  funext i; simp [dgOf, h]

lemma weight_term (hb : Bd B x I W) {d : ℕ → ℕ} (hd : ∀ i, d i ≤ I.machines) (k : ℕ)
    (hk : k < I.jobs) :
    (schedD I d ⟨k, hk⟩).elim 0 (fun _ => I.w ⟨k, hk⟩) = if d k = 0 then 0 else wt x k := by
  show (Brute.mach I (d k)).elim 0 (fun _ => I.w ⟨k, hk⟩) = _
  rw [elim_mach (hd k), hb.enc.wt_eq ⟨k, hk⟩]

theorem jobStep2_spec (hb : Bd B x I W) :
    Spec B (fun σ => JInv x I W σ ∧ σ.vars "j" < I.jobs) jobStep2
      (fun σ σ' => JInv x I W σ' ∧ σ'.vars "j" = σ.vars "j" + 1)
      (30 + (44 * x.length + 8) + 90) := by
  have hF := jobFetch_spec hb
  have hE := eligLoop_spec (B := B) (x := x) I.jobs I.machines x.length hb.xg hb.lenx hb.mB
  have hFo := jobFold_spec hb
  intro σ ⟨hJ, hj⟩
  obtain ⟨hctx, hjle, hok, hacc, hokiff, haccEq⟩ := hJ
  obtain ⟨σ1, hr1, hA, hva1, ho11, hel1⟩ := hF σ ⟨hctx, hj⟩
  have hctx1 : Ctx x I W σ1 := hctx.only hA (by decide)
  have hj1 : σ1.vars "j" = σ.vars "j" := hA.1 "j" (by decide)
  have hok1 : σ1.vars "ok" = σ.vars "ok" := hA.1 "ok" (by decide)
  have hacc1 : σ1.vars "acc" = σ.vars "acc" := hA.1 "acc" (by decide)
  have hasg1 : σ1.arrs "asg" = σ.arrs "asg" := hA.2 "asg"
  have hdg1 : dgOf σ1 = dgOf σ := dgOf_congr hasg1
  have hvaM : σ.vars "va" ≤ I.machines ∨ True := Or.inr trivial
  have hva1M : σ1.vars "va" ≤ I.machines := by rw [hva1]; exact hctx.hdig _
  have hmono := hb.enc.off_mono (σ.vars "j") hj
  have hnext : offset x (σ.vars "j" + 1) ≤ offset x I.jobs :=
    hb.enc.off_mono' I.jobs (le_refl _) _ hj
  have hoffle := hb.offle
  obtain ⟨σ2, hr2, hE1, hE2, hfle, hfiff⟩ := hE σ1
    ⟨by rw [hctx1.ha], hctx1.hT0, hva1M, by rw [ho11, hel1]; omega, by rw [hel1]; omega⟩
  have hE' : Only ["fnd", "e"] σ1 σ2 := Only.of_ne ⟨hE1, hE2⟩ rfl
  have hctx2 : Ctx x I W σ2 := hctx1.only hE' (by decide)
  have hj2 : σ2.vars "j" = σ.vars "j" := by rw [hE'.1 "j" (by decide), hj1]
  have hok2 : σ2.vars "ok" = σ.vars "ok" := by rw [hE'.1 "ok" (by decide), hok1]
  have hacc2 : σ2.vars "acc" = σ.vars "acc" := by rw [hE'.1 "acc" (by decide), hacc1]
  have hva2 : σ2.vars "va" = dgOf σ (σ.vars "j") := by rw [hE'.1 "va" (by decide), hva1]
  have hasg2 : σ2.arrs "asg" = σ.arrs "asg" := by rw [hE'.2 "asg", hasg1]
  have hva2M : σ2.vars "va" ≤ I.machines := by rw [hE'.1 "va" (by decide)]; exact hva1M
  obtain ⟨σ3, hr3, hC, hj3, hokiff3, hok3, hacc3⟩ := hFo σ2
    ⟨hctx2, by rw [hj2]; exact hj, by rw [hok2]; exact hok, by rw [hacc2]; exact hacc, hva2M, hfle⟩
  have hctx3 : Ctx x I W σ3 := hctx2.only hC (by decide)
  have hasg3 : σ3.arrs "asg" = σ.arrs "asg" := by rw [hC.2, hasg2]
  have hdg3 : dgOf σ3 = dgOf σ := dgOf_congr hasg3
  have hj3' : σ3.vars "j" = σ.vars "j" + 1 := by rw [hj3, hj2]
  have hokC : σ3.vars "ok" = 1 ↔ ElUpTo I (dgOf σ) (σ.vars "j" + 1) := by
    have h1 := mach_elig hb.enc ⟨σ.vars "j", hj⟩ (v := dgOf σ (σ.vars "j")) (hctx.hdig _)
    simp only at h1
    rw [ElUpTo_succ hj, h1, hokiff3, hok2, hokiff, hva2, hfiff, hel1, ho11, hva1]
  have haccC : σ3.vars "acc" = Brute.wacc I (schedD I (dgOf σ)) W (σ.vars "j" + 1) := by
    rw [wacc_succ_of_lt _ W _ hj, hacc3, hacc2, hj2, hva2, ← haccEq,
      weight_term hb (d := dgOf σ) (fun i => hctx.hdig i) _ hj]
  refine ⟨σ3, (hr1.seq (hr2.seq hr3)).mono (by omega), ⟨hctx3, by omega, hok3, ?_, ?_, ?_⟩, hj3'⟩
  · rw [hacc3]; exact min_le_right _ _
  · rw [hj3', hdg3]; exact hokC
  · rw [hj3', hdg3]; exact haccC

/-! ### Clashes -/

/-- The four facts a clash is made of: the digits agree and are not zero, and each job
starts before the other is due. -/
def ClashN (va vb sa da sb db : ℕ) : Prop := va = vb ∧ 0 < va ∧ sa < db ∧ sb < da

instance (va vb sa da sb db : ℕ) : Decidable (ClashN va vb sa da sb db) := by
  unfold ClashN; infer_instance

/-- Jobs `a` and `b` overlap and the digits put them on one machine. -/
def Bad (I : Instance) (d : ℕ → ℕ) (a b : ℕ) : Prop :=
  ∃ (ha : a < I.jobs) (hb : b < I.jobs), I.Overlap ⟨a, ha⟩ ⟨b, hb⟩ ∧
    ∃ v, Brute.mach I (d a) = some v ∧ Brute.mach I (d b) = some v

/-- No clash among the pairs whose first job is before `k`. -/
def PairsUpTo (I : Instance) (d : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ a b, a < k → a < b → b < I.jobs → ¬ Bad I d a b

/-- No clash of job `a` with the jobs in `(a, k)`. -/
def RowUpTo (I : Instance) (d : ℕ → ℕ) (a k : ℕ) : Prop :=
  ∀ b, a < b → b < k → b < I.jobs → ¬ Bad I d a b

lemma bad_iff (hb : Bd B x I W) {d : ℕ → ℕ} (hd : ∀ i, d i ≤ I.machines) {a b : ℕ}
    (ha : a < I.jobs) (hb' : b < I.jobs) :
    Bad I d a b ↔ ClashN (d a) (d b) (due x a - proc x a) (due x a)
      (due x b - proc x b) (due x b) := by
  have hda := hb.enc.due_eq ⟨a, ha⟩
  have hdb := hb.enc.due_eq ⟨b, hb'⟩
  have hpa := hb.enc.proc_eq ⟨a, ha⟩
  have hpb := hb.enc.proc_eq ⟨b, hb'⟩
  simp only at hda hdb hpa hpb
  constructor
  · rintro ⟨ha0, hb0, hov, v, hv1, hv2⟩
    obtain ⟨h1, h2⟩ := hov
    have hz : d a ≠ 0 := by
      intro h0; rw [h0, mach_zero] at hv1; exact absurd hv1 (by simp)
    have hz' : d b ≠ 0 := by
      intro h0; rw [h0, mach_zero] at hv2; exact absurd hv2 (by simp)
    rw [mach_pos (hd a) hz] at hv1
    rw [mach_pos (hd b) hz'] at hv2
    have := hv1.trans hv2.symm
    simp only [Option.some.injEq, Fin.mk.injEq] at this
    refine ⟨by omega, by omega, ?_, ?_⟩
    · simp only [Instance.start] at h1; omega
    · simp only [Instance.start] at h2; omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨ha, hb', ⟨?_, ?_⟩, ?_⟩
    · simp only [Instance.start]; omega
    · simp only [Instance.start]; omega
    · refine ⟨⟨d a - 1, by have := hd a; omega⟩, mach_pos (hd a) (by omega), ?_⟩
      rw [mach_pos (hd b) (by omega)]
      exact congrArg some (Fin.ext (by simp only; omega))

lemma RowUpTo_succ {d : ℕ → ℕ} {a b : ℕ} (hab : a < b) (hbn : b < I.jobs) :
    RowUpTo I d a (b + 1) ↔ RowUpTo I d a b ∧ ¬ Bad I d a b := by
  constructor
  · intro h; exact ⟨fun c h1 h2 h3 => h c h1 (by omega) h3, h b hab (by omega) hbn⟩
  · rintro ⟨h1, h2⟩ c hc1 hc2 hc3
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc2 with h | h
    · exact h1 c hc1 h hc3
    · subst h; exact h2

lemma PairsUpTo_succ {d : ℕ → ℕ} {a n : ℕ} :
    PairsUpTo I d (a + 1) ↔ PairsUpTo I d a ∧ RowUpTo I d a I.jobs := by
  constructor
  · intro h
    exact ⟨fun c b h1 h2 h3 => h c b (by omega) h2 h3, fun b h1 h2 h3 => h a b (by omega) h1 h3⟩
  · rintro ⟨h1, h2⟩ c b hc hcb hb
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h | h
    · exact h1 c b h hcb hb
    · subst h; exact h2 b hcb hb hb

/-- The value the clash expression takes. -/
def rawClash (va vb sa da sb db : ℕ) : ℕ :=
  (1 - (va - vb + (vb - va) - (va - vb + (vb - va) - 1)) + (va - (va - 1)) +
    (db - sa - (db - sa - 1) + (da - sb - (da - sb - 1)))) - 3

lemma flag_eq (a b : ℕ) : 1 - (a - b + (b - a) - (a - b + (b - a) - 1)) = if a = b then 1 else 0 := by
  split_ifs <;> omega

lemma flag_lt (a b : ℕ) : b - a - (b - a - 1) = if a < b then 1 else 0 := by
  split_ifs <;> omega

lemma flag_pos (v : ℕ) : v - (v - 1) = if 0 < v then 1 else 0 := by
  split_ifs <;> omega

lemma clash_arith (ok0 va vb sa da sb db : ℕ) (h : ok0 ≤ 1) :
    ok0 - rawClash va vb sa da sb db = 1 ↔ ok0 = 1 ∧ ¬ ClashN va vb sa da sb db := by
  unfold rawClash ClashN
  rw [flag_eq, flag_pos, flag_lt, flag_lt]
  split_ifs <;> omega

/-- The state of the inner pass over the later jobs, for the job `a` in hand. `E` is what
has been established about the schedule before the pairs. -/
def PIn (E : Prop) (x : List ℕ) (I : Instance) (W : ℕ) (a : ℕ) (σ : Env) : Prop :=
  Ctx x I W σ ∧ σ.vars "i" = a ∧ a < I.jobs ∧ a < σ.vars "b" ∧ σ.vars "b" ≤ I.jobs ∧
    σ.vars "va" = dgOf σ a ∧ σ.vars "da" = due x a ∧ σ.vars "sa" = due x a - proc x a ∧
    σ.vars "ok" ≤ 1 ∧
    (σ.vars "ok" = 1 ↔ E ∧ PairsUpTo I (dgOf σ) a ∧ RowUpTo I (dgOf σ) a (σ.vars "b"))

set_option maxHeartbeats 1600000 in
theorem pairStep_spec (hb : Bd B x I W) (E : Prop) (a : ℕ) :
    Spec B (fun σ => PIn E x I W a σ ∧ σ.vars "b" < I.jobs) pairStep
      (fun σ σ' => PIn E x I W a σ' ∧ σ'.vars "b" = σ.vars "b" + 1) 200 := by
  run_vcg
  all_goals obtain ⟨⟨ha, hn, hm, hW', hO0, hT0, hlen, hdig⟩, hi, han, hab, hbn, hva, hda, hsa, hok, hiff⟩ := ‹PIn E x I W a σ›
  all_goals have hbl : σ.vars "b" < I.jobs := ‹σ.vars "b" < I.jobs›
  all_goals have hnl := hb.nlen
  all_goals have hlx := hb.lenx
  all_goals have hdaB : due x a + 2 < B := hb.xg _
  all_goals have hdbB : due x (σ.vars "b") + 2 < B := hb.xg _
  all_goals have hpbB : proc x (σ.vars "b") + 2 < B := hb.xg _
  all_goals have hmB := hb.mB
  all_goals have hdb1 : (σ.arrs "a").getD (2 + σ.vars "n" + σ.vars "b") 0 = due x (σ.vars "b") := (by rw [ha, hn, due, hb.enc.jc])
  all_goals have hpb1 : (σ.arrs "a").getD (2 + σ.vars "b") 0 = proc x (σ.vars "b") := (by rw [ha]; rfl)
  all_goals have hdg1 := hdig (σ.vars "b")
  all_goals have haL : (σ.arrs "a").length = x.length := (by rw [ha])
  all_goals have hdga := hdig a
  all_goals have hva' : σ.vars "va" = (σ.arrs "asg").getD a 0 := hva
  all_goals have hda2 : due x a - proc x a ≤ due x a := Nat.sub_le _ _
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try rw [hdb1]
  all_goals try rw [hpb1]
  all_goals try omega
  have hkey := clash_arith (σ.vars "ok") (σ.vars "va") ((σ.arrs "asg").getD (σ.vars "b") 0)
    (σ.vars "sa") (σ.vars "da") (due x (σ.vars "b") - proc x (σ.vars "b")) (due x (σ.vars "b")) hok
  have hbad := bad_iff hb (d := dgOf σ) hdig han hbl
  refine ⟨⟨⟨ha, ?_, ?_, ?_, ?_, ?_, hlen, hdig⟩, ?_, han, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals try (simp only [Env.setVar, String.reduceEq, ↓reduceIte, dgOf] at *; try omega; try assumption)
  show σ.vars "ok" - rawClash (σ.vars "va") ((σ.arrs "asg").getD (σ.vars "b") 0) (σ.vars "sa")
      (σ.vars "da") (due x (σ.vars "b") - proc x (σ.vars "b")) (due x (σ.vars "b")) = 1 ↔
    E ∧ PairsUpTo I (dgOf σ) a ∧ RowUpTo I (dgOf σ) a (σ.vars "b" + 1)
  rw [hkey, RowUpTo_succ hab hbl, hva, hsa, hda, ← hbad, hiff]
  tauto
theorem pairInner_spec (hb : Bd B x I W) (E : Prop) (a : ℕ) :
    Spec B (PIn E x I W a) pairInner
      (fun _ σ' => PIn E x I W a σ' ∧ σ'.vars "b" = I.jobs) (204 * I.jobs + 4) := by
  refine (Spec.forRange (B := B) "b" "n" (PIn E x I W a) I.jobs 200 (204 * I.jobs + 4)
    (fun σ h => by have := h.2.2.2.2.1; have := hb.nB; omega) (fun σ h => by
      have := h.1.hn; have := hb.nB; omega)
    (fun σ h => h.1.hn) (fun σ h => h.2.2.2.2.1)
    (Spec.mono (pairStep_spec hb E a) (le_refl _)) (fun _ h => h) ?_)
  intro σ h
  omega
/-- The state of the outer pass over the pairs. -/
def OInv (E : Prop) (x : List ℕ) (I : Instance) (W : ℕ) (σ : Env) : Prop :=
  Ctx x I W σ ∧ σ.vars "i" ≤ I.jobs ∧ σ.vars "ok" ≤ 1 ∧
    (σ.vars "ok" = 1 ↔ E ∧ PairsUpTo I (dgOf σ) (σ.vars "i"))

lemma RowUpTo_self_succ (d : ℕ → ℕ) (a : ℕ) : RowUpTo I d a (a + 1) := by
  intro b h1 h2 _; omega

theorem pairFetch_spec (hb : Bd B x I W) :
    Spec B (fun σ => Ctx x I W σ ∧ σ.vars "i" < I.jobs) pairFetch
      (fun σ σ' => Only ["va", "da", "sa", "b"] σ σ' ∧ σ'.vars "b" = σ.vars "i" + 1 ∧
        σ'.vars "va" = dgOf σ (σ.vars "i") ∧ σ'.vars "da" = due x (σ.vars "i") ∧
        σ'.vars "sa" = due x (σ.vars "i") - proc x (σ.vars "i")) 60 := by
  run_vcg
  all_goals obtain ⟨ha, hn, hm, hW', hO0, hT0, hlen, hdig⟩ := ‹Ctx x I W σ›
  all_goals have hi : σ.vars "i" < I.jobs := ‹σ.vars "i" < I.jobs›
  all_goals have haL : (σ.arrs "a").length = x.length := (by rw [ha])
  all_goals have hnl := hb.nlen
  all_goals have hlx := hb.lenx
  all_goals have hmB := hb.mB
  all_goals have hnB := hb.nB
  all_goals have hdaB : due x (σ.vars "i") + 2 < B := hb.xg _
  all_goals have hpaB : proc x (σ.vars "i") + 2 < B := hb.xg _
  all_goals have hda1 : (σ.arrs "a").getD (2 + σ.vars "n" + σ.vars "i") 0 = due x (σ.vars "i") := (by rw [ha, hn, due, hb.enc.jc])
  all_goals have hpa1 : (σ.arrs "a").getD (2 + σ.vars "i") 0 = proc x (σ.vars "i") := (by rw [ha]; rfl)
  all_goals have hdg1 := hdig (σ.vars "i")
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try rw [hda1]
  all_goals try rw [hpa1]
  all_goals try omega
  refine ⟨⟨fun y hy => ?_, fun a => rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3, h4⟩ := hy
    simp [h1, h2, h3, h4]
  all_goals first | trivial | rfl | simp [dgOf]

theorem bumpI_spec (hb : Bd B x I W) :
    Spec B (fun σ => σ.vars "i" < I.jobs) (bump "i")
      (fun σ σ' => Only ["i"] σ σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 10 := by
  run_vcg
  all_goals have hi : σ.vars "i" < I.jobs := ‹σ.vars "i" < I.jobs›
  all_goals have hnB := hb.nB
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try omega
  refine ⟨⟨fun y hy => ?_, fun a => rfl⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [hy]
  all_goals first | trivial | rfl

theorem pairOuterStep_spec (hb : Bd B x I W) (E : Prop) :
    Spec B (fun σ => OInv E x I W σ ∧ σ.vars "i" < I.jobs) pairOuterStep
      (fun σ σ' => OInv E x I W σ' ∧ σ'.vars "i" = σ.vars "i" + 1)
      (60 + (204 * I.jobs + 4) + 10) := by
  intro σ ⟨hO, hi⟩
  obtain ⟨hctx, hile, hok, hiff⟩ := hO
  obtain ⟨σ1, hr1, hA, hb1, hva1, hda1, hsa1⟩ := pairFetch_spec hb σ ⟨hctx, hi⟩
  have hctx1 : Ctx x I W σ1 := hctx.only hA (by decide)
  have hi1 : σ1.vars "i" = σ.vars "i" := hA.1 "i" (by decide)
  have hok1 : σ1.vars "ok" = σ.vars "ok" := hA.1 "ok" (by decide)
  have hdg1 : dgOf σ1 = dgOf σ := dgOf_congr (hA.2 "asg")
  have hP1 : PIn E x I W (σ.vars "i") σ1 := by
    refine ⟨hctx1, hi1, hi, by omega, by omega, by rw [hva1, hdg1], hda1, hsa1,
      by rw [hok1]; exact hok, ?_⟩
    rw [hok1, hdg1, hb1, hiff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, RowUpTo_self_succ _ _⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  obtain ⟨σ2, hr2, hP2, hb2⟩ := pairInner_spec hb E (σ.vars "i") σ1 hP1
  obtain ⟨hc2, hi2, -, -, -, -, -, -, hok2, hiff2⟩ := hP2
  have hi2' : σ2.vars "i" < I.jobs := by rw [hi2]; exact hi
  obtain ⟨σ3, hr3, hB, hi3⟩ := bumpI_spec hb σ2 hi2'
  have hc3 : Ctx x I W σ3 := hc2.only hB (by decide)
  have hok3 : σ3.vars "ok" = σ2.vars "ok" := hB.1 "ok" (by decide)
  have hdg3 : dgOf σ3 = dgOf σ2 := dgOf_congr (hB.2 "asg")
  refine ⟨σ3, (hr1.seq (hr2.seq hr3)).mono (by omega), ⟨hc3, by omega, by rw [hok3]; exact hok2, ?_⟩,
    by omega⟩
  rw [hok3, hdg3, hi3, hi2, PairsUpTo_succ, hiff2, hb2]
  tauto

theorem pairsLoop_spec (hb : Bd B x I W) (E : Prop) :
    Spec B (fun σ => OInv E x I W (σ.setVar "i" 0))
      (.seq (set "i" (lit 0)) (.while (.lt (V "i") (V "n")) pairOuterStep))
      (fun _ σ' => OInv E x I W σ' ∧ σ'.vars "i" = I.jobs)
      ((60 + (204 * I.jobs + 4) + 10 + 4) * I.jobs + 6) :=
  Spec.forRangeZero (B := B) "i" "n" (OInv E x I W) I.jobs (60 + (204 * I.jobs + 4) + 10)
    (by have := hb.nB; omega) (fun σ h => h.2.1) (fun σ h => h.1.hn)
    (pairOuterStep_spec hb E)

theorem jobsLoop_spec (hb : Bd B x I W) :
    Spec B (fun σ => JInv x I W (σ.setVar "j" 0)) jobsLoop
      (fun _ σ' => JInv x I W σ' ∧ σ'.vars "j" = I.jobs)
      ((44 * x.length + 128 + 4) * I.jobs + 6) :=
  Spec.forRangeZero (B := B) "j" "n" (JInv x I W) I.jobs (44 * x.length + 128)
    (by have := hb.nB; omega) (fun σ h => h.2.1) (fun σ h => h.1.hn)
    (Spec.mono (jobStep2_spec hb) (by omega))

lemma feasible_iff_digits (d : ℕ → ℕ) :
    Feasible (schedD I d) ↔ ElUpTo I d I.jobs ∧ PairsUpTo I d I.jobs := by
  rw [Brute.feasible_iff]
  constructor
  · rintro ⟨he, hc⟩
    refine ⟨fun j _ i h => he j i h, fun a b ha hab hb hbad => ?_⟩
    obtain ⟨ha', hb', hov, v, h1, h2⟩ := hbad
    exact hc ⟨a, ha'⟩ ⟨b, hb'⟩ hab hov v h1 h2
  · rintro ⟨he, hp⟩
    refine ⟨fun j i h => he j j.isLt i h, fun a b hab hov v h1 h2 => ?_⟩
    exact hp a.val b.val a.isLt hab b.isLt ⟨a.isLt, b.isLt, hov, v, h1, h2⟩

/-- **One string, tested.** `ok` says whether the schedule the digits read is feasible, and
`acc` holds its weight, capped at `W`. -/
theorem evalOne_spec (hb : Bd B x I W) :
    Spec B (fun σ => Ctx x I W σ) evalOne
      (fun σ σ' => Ctx x I W σ' ∧ σ'.arrs "asg" = σ.arrs "asg" ∧
        σ'.vars "ans" = σ.vars "ans" ∧ σ'.vars "dn" = σ.vars "dn" ∧ σ'.vars "ok" ≤ 1 ∧
        (σ'.vars "ok" = 1 ↔ Feasible (schedD I (dgOf σ))) ∧
        σ'.vars "acc" = Brute.wacc I (schedD I (dgOf σ)) W I.jobs)
      (4 + ((44 * x.length + 128 + 4) * I.jobs + 6) +
        ((60 + (204 * I.jobs + 4) + 10 + 4) * I.jobs + 6)) := by
  intro σ hctx
  have hn := hb.nB
  have hra : Run B (set "ok" (lit 1)) σ (σ.setVar "ok" 1) 2 :=
    (Run.assign (v := 1) (SweepBody.evalB_lit (by omega))).mono (by norm_num [Expr.size])
  have hrb : Run B (set "acc" (lit 0)) (σ.setVar "ok" 1) ((σ.setVar "ok" 1).setVar "acc" 0) 2 :=
    (Run.assign (v := 0) (SweepBody.evalB_lit (by omega))).mono (by norm_num [Expr.size])
  set σ0 := (σ.setVar "ok" 1).setVar "acc" 0 with hσ0
  have hO0 : Only ["ok", "acc", "j"] σ (σ0.setVar "j" 0) := by
    refine ⟨fun y hy => ?_, fun a => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3⟩ := hy
    simp [hσ0, Env.setVar, h1, h2, h3]
  have hJ0 : JInv x I W (σ0.setVar "j" 0) := by
    refine ⟨hctx.only hO0 (by decide), by simp [Env.setVar], by simp [Env.setVar, hσ0],
      by simp [Env.setVar, hσ0], ?_, ?_⟩
    · simp [Env.setVar, hσ0, ElUpTo]
    · simp [Env.setVar, hσ0, Brute.wacc]
  obtain ⟨σ1, hr1, hJ1, hj1⟩ := jobsLoop_spec hb (σ0) hJ0
  have hdgA : σ1.arrs "asg" = σ.arrs "asg" := by
    rw [hr1.frame_arr "asg" (by simp [jobsLoop, jobStep2, jobFetch, eligLoop, eligStep,
      jobFold, Com.warrs])]
    rfl
  have hdg1 : dgOf σ1 = dgOf σ := dgOf_congr hdgA
  have hOI : OInv (ElUpTo I (dgOf σ) I.jobs) x I W (σ1.setVar "i" 0) := by
    have hOn : Only ["i"] σ1 (σ1.setVar "i" 0) := by
      refine ⟨fun y hy => ?_, fun a => rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      simp [Env.setVar, hy]
    refine ⟨hJ1.1.only hOn (by decide), by simp [Env.setVar], by simpa [Env.setVar] using hJ1.2.2.1, ?_⟩
    have := hJ1.2.2.2.2.1
    simp only [Env.setVar, ↓reduceIte, String.reduceEq]
    rw [this, hj1]
    rw [show dgOf σ1 = dgOf σ from hdg1] at *
    constructor
    · intro h; exact ⟨h, fun a b h' => absurd h' (Nat.not_lt_zero _)⟩
    · rintro ⟨h, -⟩; exact h
  obtain ⟨σ2, hr2, hO2, hi2⟩ := pairsLoop_spec hb (ElUpTo I (dgOf σ) I.jobs) σ1 hOI
  have hasg2 : σ2.arrs "asg" = σ.arrs "asg" := by
    rw [hr2.frame_arr "asg" (by simp [pairsLoop, pairOuterStep, pairFetch, pairInner, pairStep,
      Com.warrs]), hdgA]
  have hdg2 : dgOf σ2 = dgOf σ := dgOf_congr hasg2
  have hans : σ2.vars "ans" = σ.vars "ans" := by
    rw [hr2.frame_var "ans" (by simp [pairsLoop, pairOuterStep, pairFetch, pairInner,
      pairStep, Com.wvars]),
      hr1.frame_var "ans" (by simp [jobsLoop, jobStep2, jobFetch, eligLoop, eligStep,
        jobFold, Com.wvars])]
    simp [hσ0, Env.setVar]
  have hdn : σ2.vars "dn" = σ.vars "dn" := by
    rw [hr2.frame_var "dn" (by simp [pairsLoop, pairOuterStep, pairFetch, pairInner,
      pairStep, Com.wvars]),
      hr1.frame_var "dn" (by simp [jobsLoop, jobStep2, jobFetch, eligLoop, eligStep,
        jobFold, Com.wvars])]
    simp [hσ0, Env.setVar]
  have hacc2 : σ2.vars "acc" = σ1.vars "acc" :=
    hr2.frame_var "acc" (by simp [pairsLoop, pairOuterStep, pairFetch, pairInner, pairStep,
      Com.wvars])
  refine ⟨σ2, (hra.seq (hrb.seq (hr1.seq hr2))).mono (by omega), hO2.1, hasg2, hans, hdn, hO2.2.2.1, ?_, ?_⟩
  · rw [feasible_iff_digits, hO2.2.2.2, hdg2, hi2]
  · rw [hacc2, hJ1.2.2.2.2.2, hj1, hdg1]

end JobStep
