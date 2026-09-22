import Lax470956Proofs.SweepLoop
import Lax470956Proofs.ReadHdr
import Lax470956.InstanceEncoding
import Lax470956Proofs.SweepTable

/-!
One turn of the sweep's outer loop.
-/

namespace Lax470956Proofs.SweepBody

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.Scheduling Lax470956.Scheduling.Instance Lax470956.Preprocessing
open Lax470956.InstanceEncoding
open Lax470956Proofs.FreeDP Lax470956Proofs.SweepDP Lax470956Proofs.SweepLoop
open Lax470956Proofs.SweepProg Lax470956Proofs.SweepTable

variable {B : ℕ} {I : Instance} {P n S C : ℕ} {ord : ℕ → Fin I.jobs} {dl : ℕ → ℕ}
  {nc : ℕ → Bool} {x : List ℕ}

/-- What does not change while the sweep runs. -/
structure Ctx (I : Instance) (P n S C : ℕ) (ord : ℕ → Fin I.jobs) (dl : ℕ → ℕ)
    (nc : ℕ → Bool) (x : List ℕ) (σ : Env) : Prop where
  arrA : σ.arrs "a" = x
  varn : σ.vars "n" = n
  varm : σ.vars "m" = I.machines
  varP : σ.vars "P" = P
  varS : σ.vars "S" = S
  varcap : σ.vars "cap" = C
  varO0 : σ.vars "O0" = 2 + 3 * I.jobs
  varT0 : σ.vars "T0" = 3 + 4 * I.jobs
  pw : Pw I.machines P σ
  ordA : ∀ k, k < n → (σ.arrs "ord").getD k 0 = (ord k).val
  dlA : ∀ k, k < n → (σ.arrs "dl").getD k 0 = dl k
  ncA : ∀ k, k < n → (σ.arrs "nc").getD k 0 = if nc k then 1 else 0
  lenV : (σ.arrs "V").length = S
  lenV2 : (σ.arrs "V2").length = S
  lenVt : (σ.arrs "Vt").length = S
  lenOrd : n ≤ (σ.arrs "ord").length
  lenDl : n ≤ (σ.arrs "dl").length
  lenNc : n ≤ (σ.arrs "nc").length

/-- The scalars and arrays the context speaks of. -/
def ctxVars : List String := ["n", "m", "P", "S", "cap", "O0", "T0"]

def ctxArrs : List String := ["a", "pw", "ord", "dl", "nc"]

lemma Ctx.congr {σ σ' : Env} (h : Ctx I P n S C ord dl nc x σ)
    (hv : ∀ y ∈ ctxVars, σ'.vars y = σ.vars y)
    (ha : ∀ a ∈ ctxArrs, σ'.arrs a = σ.arrs a)
    (hV : (σ'.arrs "V").length = S) (hV2 : (σ'.arrs "V2").length = S)
    (hVt : (σ'.arrs "Vt").length = S) : Ctx I P n S C ord dl nc x σ' where
  arrA := by rw [ha "a" (by decide)]; exact h.arrA
  varn := by rw [hv "n" (by decide)]; exact h.varn
  varm := by rw [hv "m" (by decide)]; exact h.varm
  varP := by rw [hv "P" (by decide)]; exact h.varP
  varS := by rw [hv "S" (by decide)]; exact h.varS
  varcap := by rw [hv "cap" (by decide)]; exact h.varcap
  varO0 := by rw [hv "O0" (by decide)]; exact h.varO0
  varT0 := by rw [hv "T0" (by decide)]; exact h.varT0
  pw := by rw [Pw, ha "pw" (by decide)]; exact h.pw
  ordA := by intro k hk; rw [ha "ord" (by decide)]; exact h.ordA k hk
  dlA := by intro k hk; rw [ha "dl" (by decide)]; exact h.dlA k hk
  ncA := by intro k hk; rw [ha "nc" (by decide)]; exact h.ncA k hk
  lenV := hV
  lenV2 := hV2
  lenVt := hVt
  lenOrd := by rw [ha "ord" (by decide)]; exact h.lenOrd
  lenDl := by rw [ha "dl" (by decide)]; exact h.lenDl
  lenNc := by rw [ha "nc" (by decide)]; exact h.lenNc

/-! ### The eligibility scan -/

/-- The machines the word lists for the job at `jb`, as far as `e`. -/
def eligList (I : Instance) (x : List ℕ) (jb : ℕ) (i0 : Fin I.machines)
    (hx : ∀ t, t < offset x I.jobs → target x t < I.machines) (e : ℕ) :
    List (Fin I.machines) :=
  (List.range e).map fun r =>
    if h : offset x jb + r < offset x I.jobs then ⟨target x (offset x jb + r), hx _ h⟩ else i0

lemma eligList_succ (I : Instance) (x : List ℕ) (jb : ℕ) (i0 : Fin I.machines)
    (hx : ∀ t, t < offset x I.jobs → target x t < I.machines) (e : ℕ) :
    eligList I x jb i0 hx (e + 1) = eligList I x jb i0 hx e ++
      [if h : offset x jb + e < offset x I.jobs then ⟨target x (offset x jb + e), hx _ h⟩
        else i0] := by
  unfold eligList
  rw [List.range_succ, List.map_append]
  rfl

variable (I P n S C ord dl nc x) in
/-- The state of the eligibility scan. -/
def EInv (jb pj wj elen : ℕ) (T : ℕ → ℕ) (E : ℕ → List (Fin I.machines)) (σ : Env) : Prop :=
  Ctx I P n S C ord dl nc x σ ∧ σ.vars "pj" = pj ∧ σ.vars "wj" = wj ∧
    σ.vars "jb" = jb ∧ σ.vars "o1" = offset x jb ∧ σ.vars "elen" = elen ∧
    σ.vars "e" ≤ elen ∧
    Tbl "V" S T σ ∧ Tbl "V2" S (foldRelax P I pj wj (C + 1) T (E (σ.vars "e")) T) σ

theorem entryBody_spec (jb pj wj elen : ℕ) (T : ℕ → ℕ) (i0 : Fin I.machines)
    (hx : ∀ t, t < offset x I.jobs → target x t < I.machines)
    (hin : ∀ r, r < elen → offset x jb + r < offset x I.jobs)
    (hxg : ∀ i, x.getD i 0 + 2 < B) (hSB : S + 2 < B) (hS : S = (P + 1) ^ I.machines)
    (hmB : I.machines + 2 < B) (hPB : P + 2 < B) (hpjB : pj < B) (hCB : C + wj + 3 < B)
    (hTC : ∀ c, T c ≤ C + 1) (hlenx : x.length + 2 < B) (helen : elen + 2 < B)

    (hshape : 3 + 4 * I.jobs + offset x I.jobs ≤ x.length) (hjc : jobCount x = I.jobs) :
    Spec B (fun σ => EInv I P n S C ord dl nc x jb pj wj elen T (eligList I x jb i0 hx) σ ∧
        σ.vars "e" < elen) entryBody
      (fun σ σ' => EInv I P n S C ord dl nc x jb pj wj elen T (eligList I x jb i0 hx) σ' ∧
        σ'.vars "e" = σ.vars "e" + 1) (84 * S + 20) := by
  have hSle : (P + 1) ^ I.machines ≤ S := le_of_eq hS.symm
  run_vcg [(relaxLoop_specG (B := B) I.machines P S (C + 1) (C + 1) T
      hSB hSle hmB hPB (fun c => hTC c) (le_refl _)).frame]
  all_goals obtain ⟨hctx, hpjv, hwjv, hjbv, ho1v, helenv, hele, hTV, hTV2⟩ :=
    ‹EInv I P n S C ord dl nc x jb pj wj elen T (eligList I x jb i0 hx) σ›
  all_goals have helt : σ.vars "e" < elen := ‹σ.vars "e" < elen›
  all_goals have hrange : offset x jb + σ.vars "e" < offset x I.jobs := hin _ helt
  all_goals have hidx : σ.vars "T0" + (σ.vars "o1" + σ.vars "e")
      = 3 + 4 * jobCount x + (offset x jb + σ.vars "e") := (by
    rw [hctx.varT0, ho1v, hjc])
  all_goals have htgt : (σ.arrs "a").getD (σ.vars "T0" + (σ.vars "o1" + σ.vars "e")) 0
      = target x (offset x jb + σ.vars "e") := (by rw [hctx.arrA, hidx]; rfl)
  all_goals have hmi : target x (offset x jb + σ.vars "e") < I.machines := hx _ hrange
  all_goals have ho1B : σ.vars "o1" + 2 < B := (by rw [ho1v]; exact hxg _)
  all_goals have hT0 : σ.vars "T0" = 3 + 4 * I.jobs := hctx.varT0
  all_goals have haL : (σ.arrs "a").length = x.length := (by rw [hctx.arrA])
  all_goals have hmiB : target x (offset x jb + σ.vars "e") + 2 < B := hxg _
  all_goals try
    (obtain ⟨⟨hT2', hTV', hSv'⟩, hfv, hfa, -, -⟩ := ‹(_ ∧ _ ∧ _) ∧ (∀ y ∉ relaxLoop.wvars, _) ∧ _›
     have hfn := hfv "n" (by simp [wvars_relaxLoop])
     have hfm := hfv "m" (by simp [wvars_relaxLoop])
     have hfP := hfv "P" (by simp [wvars_relaxLoop])
     have hfS := hfv "S" (by simp [wvars_relaxLoop])
     have hfcap := hfv "cap" (by simp [wvars_relaxLoop])
     have hfO0 := hfv "O0" (by simp [wvars_relaxLoop])
     have hfT0 := hfv "T0" (by simp [wvars_relaxLoop])
     have hfjb := hfv "jb" (by simp [wvars_relaxLoop])
     have hfo1 := hfv "o1" (by simp [wvars_relaxLoop])
     have hfe := hfv "e" (by simp [wvars_relaxLoop])
     have hfelen := hfv "elen" (by simp [wvars_relaxLoop])
     have hfpj := hfv "pj" (by simp [wvars_relaxLoop])
     have hfwj := hfv "wj" (by simp [wvars_relaxLoop])
     have hfa' := hfa "a" (by simp [warrs_relaxLoop])
     have hfpw := hfa "pw" (by simp [warrs_relaxLoop])
     have hford := hfa "ord" (by simp [warrs_relaxLoop])
     have hfdl := hfa "dl" (by simp [warrs_relaxLoop])
     have hfnc := hfa "nc" (by simp [warrs_relaxLoop])
     have hfV := hfa "V" (by simp [warrs_relaxLoop])
     have hfVt := hfa "Vt" (by simp [warrs_relaxLoop])
     simp only [Env.setVar, String.reduceEq, ↓reduceIte] at hfn hfm hfP hfS hfcap hfO0
     simp only [Env.setVar, String.reduceEq, ↓reduceIte] at hfT0 hfjb hfo1 hfe hfpj hfwj hfelen
     simp only [Env.setVar, String.reduceEq, ↓reduceIte] at hfa' hfpw hford hfdl hfnc hfV hfVt)
  · refine ⟨⟨hctx.congr (fun y hy => ?_) (fun a ha => ?_) ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩, by simp [Env.setVar, hfe]⟩
    · simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
      simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hfn
      · exact hfm
      · exact hfP
      · exact hfS
      · exact hfcap
      · exact hfO0
      · exact hfT0
    · simp only [ctxArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      simp only [Env.setVar]
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · exact hfa'
      · exact hfpw
      · exact hford
      · exact hfdl
      · exact hfnc
    · simp only [Env.setVar]; rw [hfV]; exact hctx.lenV
    · simp only [Env.setVar]; exact hT2'.1
    · simp only [Env.setVar]; rw [hfVt]; exact hctx.lenVt
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [hfpj]; exact hpjv
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [hfwj]; exact hwjv
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [hfjb]; exact hjbv
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [hfo1]; exact ho1v
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [hfelen]; exact helenv
    · simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [hfe]; omega
    · simp only [Env.setVar, Tbl]; rw [hfV]; exact hTV
    · simp only [Env.setVar, Tbl, String.reduceEq, ↓reduceIte]
      rw [hfe, eligList_succ, foldRelax_snoc, dif_pos hrange]
      refine ⟨hT2'.1, fun c hc => ?_⟩
      have h2 := hT2'.2 c hc
      simp only [Env.setVar, String.reduceEq, ↓reduceIte, htgt] at h2
      rw [hpjv, hwjv] at h2
      rw [relaxed_congr_g (g' := foldRelax P I pj wj (C + 1) T
        (eligList I x jb i0 hx (σ.vars "e")) T) (hTV2.2 c hc), hS] at h2
      exact h2
  all_goals first
    | omega
    | (rw [hT0]; omega)
    | (rw [hT0, ho1v]; omega)
    | (rw [hT0, ho1v, haL]; omega)
    | (rw [htgt]; omega)
    | (rw [hfe]; omega)
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Env.setVar, String.reduceEq, ↓reduceIte, Tbl, Pw, htgt] <;>
        first
          | exact hctx.varS
          | exact hctx.varP
          | exact hmi
          | (rw [hctx.varcap])
          | exact hctx.pw
          | exact hTV
          | exact hTV2
          | (rw [hpjv]; omega)
          | (rw [hwjv]; omega)
          | exact hTV2.1
          | (intro c
             by_cases hcS : c < S
             · rw [hTV2.2 c hcS]
               exact foldRelax_le _ _ _ _ _ _ _ (fun k => hTC k) (le_refl _) c
             · rw [List.getD_eq_getElem?_getD,
                 List.getElem?_eq_none (by rw [hTV2.1]; omega)]
               simp)
          | (rw [hpjv]; exact hpjB)
          | omega)

/-- **The eligibility scan.** -/
theorem entryLoop_spec (jb pj wj elen : ℕ) (T : ℕ → ℕ) (i0 : Fin I.machines)
    (hx : ∀ t, t < offset x I.jobs → target x t < I.machines)
    (hin : ∀ r, r < elen → offset x jb + r < offset x I.jobs)
    (hxg : ∀ i, x.getD i 0 + 2 < B) (hSB : S + 2 < B) (hS : S = (P + 1) ^ I.machines)
    (hmB : I.machines + 2 < B) (hPB : P + 2 < B) (hpjB : pj < B) (hCB : C + wj + 3 < B)
    (hTC : ∀ c, T c ≤ C + 1) (hlenx : x.length + 2 < B) (helen : elen + 2 < B)
    (hshape : 3 + 4 * I.jobs + offset x I.jobs ≤ x.length) (hjc : jobCount x = I.jobs) :
    Spec B (fun σ => Ctx I P n S C ord dl nc x σ ∧ σ.vars "pj" = pj ∧ σ.vars "wj" = wj ∧
        σ.vars "jb" = jb ∧ σ.vars "o1" = offset x jb ∧ σ.vars "elen" = elen ∧
        Tbl "V" S T σ ∧ Tbl "V2" S T σ) entryLoop
      (fun _ σ' => Ctx I P n S C ord dl nc x σ' ∧ Tbl "V" S T σ' ∧
        Tbl "V2" S (foldRelax P I pj wj (C + 1) T (eligList I x jb i0 hx elen) T) σ' ∧
        σ'.vars "jb" = jb) ((84 * S + 24) * elen + 6) := by
  intro σ ⟨hctx, hpjv, hwjv, hjbv, ho1v, helenv, hTV, hTV2⟩
  obtain ⟨σ', hrun, hI, he⟩ :=
    Spec.forRangeZero (B := B) "e" "elen"
      (EInv I P n S C ord dl nc x jb pj wj elen T (eligList I x jb i0 hx)) elen (84 * S + 20)
      (by omega) (fun _ h => h.2.2.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.1)
      (entryBody_spec jb pj wj elen T i0 hx hin hxg hSB hS hmB hPB hpjB hCB hTC hlenx helen
        hshape hjc) σ
      ⟨hctx.congr (fun y hy => by
          simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Env.setVar])
        (fun a _ => by simp [Env.setVar])
        (by simpa [Env.setVar] using hctx.lenV) (by simpa [Env.setVar] using hctx.lenV2)
        (by simpa [Env.setVar] using hctx.lenVt),
        by simpa [Env.setVar] using hpjv, by simpa [Env.setVar] using hwjv,
        by simpa [Env.setVar] using hjbv, by simpa [Env.setVar] using ho1v,
        by simpa [Env.setVar] using helenv, by simp [Env.setVar],
        by simpa [Env.setVar, Tbl] using hTV,
        by simpa [Env.setVar, Tbl, eligList, foldRelax] using hTV2⟩
  obtain ⟨hctx', -, -, hjb', -, -, -, hTV', hTV2'⟩ := hI
  rw [he] at hTV2'
  exact ⟨σ', hrun.mono (le_of_eq (by ring)), hctx', hTV', hTV2', hjb'⟩

/-! ### The loop invariant -/

variable (I P n S C ord dl nc x) in
/-- The sweep, between jobs. -/
def LInv (σ : Env) : Prop :=
  Ctx I P n S C ord dl nc x σ ∧ σ.vars "k" ≤ n ∧
    σ.vars "tp" = (if σ.vars "k" = 0 then 0 else dl (σ.vars "k" - 1)) ∧
    σ.vars "acc" = min (optimumOn I (seg ord 0 (cut nc (σ.vars "k"))).toFinset) C ∧
    ∃ T, Tbl "V" S T σ ∧
      Tab (I := I) (P := P) C (seg ord (cut nc (σ.vars "k")) (σ.vars "k")) (σ.vars "tp") T

lemma refOf_seg (hO : Order I P n ord dl nc) {a k : ℕ} (hk : k ≤ n) (hak : a ≤ k) :
    refOf I 0 (seg ord a k) = if a = k then 0 else dl (k - 1) := by
  rcases Nat.eq_or_lt_of_le hak with rfl | hlt
  · simp [refOf]
  · rw [if_neg (by omega)]
    have hk1 : k = (k - 1) + 1 := by omega
    rw [hk1, seg_succ ord (by omega), refOf_snoc]
    rw [show k - 1 + 1 - 1 = k - 1 from by omega]
    exact (hO.dl_eq (k - 1) (by omega)).symm

lemma tp_le (hO : Order I P n ord dl nc) {k : ℕ} (hk : k < n) (htp : ℕ)
    (hteq : htp = if k = 0 then 0 else dl (k - 1)) (hnc : nc k = false) : htp ≤ dl k := by
  subst hteq
  by_cases hk0 : k = 0
  · simp [hk0]
  · rw [if_neg hk0]
    exact hO.mono k hk hnc (by omega)

/-- The bounds the sweep runs under. -/
structure Bnd (B : ℕ) (I : Instance) (P n S C : ℕ) (dl : ℕ → ℕ) (x : List ℕ) : Prop where
  size : S = (P + 1) ^ I.machines
  sB : S + 2 < B
  mB : I.machines + 2 < B
  pB : P + 2 < B
  cB : 2 * C + 4 < B
  xg : ∀ i, x.getD i 0 + 2 < B
  lenx : x.length + 2 < B
  nB : n + 2 < B
  dlB : ∀ k, k < n → S + P + dl k + 2 < B
  wB : ∀ i, C + x.getD i 0 + 3 < B

/-! ### Two small facts about running a command -/

/-- No command can change the length of an array: the only way to touch one is a store,
and a store overwrites a cell. -/
lemma bigStep_arrs_length {c : Com} {σ σ' : Env} {kk : ℕ} (h : BigStep c σ σ' kk)
    (nm : String) : (σ'.arrs nm).length = (σ.arrs nm).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [Env.setArr]; split <;> simp_all
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

lemma run_arrs_length {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (nm : String) : (σ'.arrs nm).length = (σ.arrs nm).length := by
  obtain ⟨kk, -, hbs⟩ := h.bigStep
  exact bigStep_arrs_length hbs nm

export Lax470956Proofs.ReadHdr (evalB_lit evalB_var evalB_add evalB_sub evalB_mul
  evalB_getE evalB_getvar)

/-! ### Setting the table up for one job -/

variable (I P n S C ord dl nc x) in
/-- What `startJob` leaves behind: the table has been carried to the job's deadline,
and the block it belongs to has been opened. -/
def JA1 (k : ℕ) (σ : Env) : Prop :=
  Ctx I P n S C ord dl nc x σ ∧ σ.vars "k" = k ∧ σ.vars "jb" = (ord k).val ∧
    σ.vars "tp" = (if k = 0 then 0 else dl (k - 1)) ∧
    σ.vars "acc" = min (optimumOn I (seg ord 0 (cut nc k)).toFinset) C ∧
    ∃ T, Tbl "V" S T σ ∧
      Tab (I := I) (P := P) C (seg ord (cut nc k) k) (σ.vars "tp") T

variable (I P n S C ord dl nc x) in
/-- …and its deadline. -/
def JA2 (k : ℕ) (σ : Env) : Prop := JA1 I P n S C ord dl nc x k σ ∧ σ.vars "t" = dl k

variable (I P n S C ord dl nc x) in
/-- After the block that ends here has been closed, if one did. -/
def JA3 (k : ℕ) (σ : Env) : Prop :=
  Ctx I P n S C ord dl nc x σ ∧ σ.vars "k" = k ∧ σ.vars "jb" = (ord k).val ∧
    σ.vars "t" = dl k ∧
    σ.vars "acc" = min (optimumOn I (seg ord 0 (cut nc (k + 1))).toFinset) C ∧
    refOf I 0 (seg ord (cut nc (k + 1)) k) ≤ σ.vars "tp" ∧ σ.vars "tp" ≤ dl k ∧
    ∃ T, Tbl "V" S T σ ∧
      Tab (I := I) (P := P) C (seg ord (cut nc (k + 1)) k) (σ.vars "tp") T

variable (I P n S C ord dl nc x) in
/-- …with the time to be made up in hand. -/
def JA4 (k : ℕ) (σ : Env) : Prop :=
  JA3 I P n S C ord dl nc x k σ ∧ σ.vars "del" = dl k - σ.vars "tp"

variable (I P n S C ord dl nc x) in
/-- After time has run: the table stands at the job's deadline. -/
def JA5 (k : ℕ) (σ : Env) : Prop :=
  Ctx I P n S C ord dl nc x σ ∧ σ.vars "k" = k ∧ σ.vars "jb" = (ord k).val ∧
    σ.vars "t" = dl k ∧
    σ.vars "acc" = min (optimumOn I (seg ord 0 (cut nc (k + 1))).toFinset) C ∧
    ∃ T, Tbl "V" S T σ ∧ Tbl "V2" S T σ ∧
      Tab (I := I) (P := P) C (seg ord (cut nc (k + 1)) k) (dl k) T

variable (I P n S C ord dl nc x) in
/-- What `startJob` leaves behind. -/
def JDone (k : ℕ) (σ : Env) : Prop :=
  JA5 I P n S C ord dl nc x k σ ∧ σ.vars "tp" = dl k

/-! ### What the passes do not write -/

lemma notMem_closeBlock {y : String} (h : y ∉ ["bst", "c", "acc"]) : y ∉ closeBlock.wvars :=
  fun hm => h (wvars_closeBlock y hm)

lemma notMemA_closeBlock (a : String) : a ∉ closeBlock.warrs := by
  simp [warrs_closeBlock]

lemma notMem_clearLoop {y : String} (h : y ∉ ["c", "tp"]) : y ∉ clearLoop.wvars :=
  fun hm => h (wvars_clearLoop y hm)

lemma notMemA_clearLoop {a : String} (h : a ∉ ["V"]) : a ∉ clearLoop.warrs :=
  fun hm => h (warrs_clearLoop a hm)

lemma notMem_commitLoop {y : String} (h : y ∉ ["c", "c2", "i", "u"]) : y ∉ commitLoop.wvars :=
  fun hm => h (wvars_commitLoop y hm)

lemma notMemA_commitLoop {a : String} (h : a ∉ ["Vt", "V", "V2"]) : a ∉ commitLoop.warrs :=
  fun hm => h (warrs_commitLoop a hm)

/-- Reading the block flag. -/
lemma nc_cond {σ : Env} {k : ℕ} (hctx : Ctx I P n S C ord dl nc x σ) (hkv : σ.vars "k" = k)
    (hk : k < n) (hkB : k < B) (hB1 : 1 < B) :
    (Cond.eq (Expr.get "nc" (V "k")) (lit 1)).evalB B σ = some (nc k) := by
  have hv : (if nc k then 1 else 0) < B := by cases nc k <;> simp <;> omega
  have h := evalB_getvar (B := B) hkB hv hkv (lt_of_lt_of_le hk hctx.lenNc) (hctx.ncA k hk)
  simp only [Cond.evalB, h]
  cases nc k <;> simp [Expr.evalB, fit_self hB1]

/-! ### `startJob`, one phase at a time -/

/-- Two capped totals add up to the capped total. -/
lemma min_add_min (a b c : ℕ) : min (min a c + (min b c + 1 - 1)) c = min (a + b) c := by omega

theorem head1_spec (hO : Order I P n ord dl nc) (hB : Bnd B I P n S C dl x) (k : ℕ)
    (hk : k < n) :
    Spec B (fun σ => LInv I P n S C ord dl nc x σ ∧ σ.vars "k" = k)
      (.assign "jb" (.get "ord" (V "k")))
      (fun _ σ' => JA1 I P n S C ord dl nc x k σ') 3 := by
  intro σ ⟨⟨hctx, hkn, htpv, haccv, T, hTV, hTab⟩, hkv⟩
  rw [hkv] at htpv haccv hTab
  have hkB : k < B := by have := hB.nB; omega
  have hjobB : (ord k).val < B := by
    have h1 : (ord k).val < I.jobs := (ord k).isLt
    have h2 : n = I.jobs := hO.len
    have := hB.nB; omega
  refine ⟨σ.setVar "jb" ((ord k).val),
    (Run.assign (evalB_getvar hkB hjobB hkv (lt_of_lt_of_le hk hctx.lenOrd)
      (hctx.ordA k hk))).mono (by norm_num [Expr.size]),
    ?_, ?_, ?_, ?_, ?_, T, ?_, ?_⟩
  · exact hctx.congr (fun y hy => by
        simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Env.setVar])
      (fun a _ => by simp [Env.setVar])
      (by simpa [Env.setVar] using hctx.lenV) (by simpa [Env.setVar] using hctx.lenV2)
      (by simpa [Env.setVar] using hctx.lenVt)
  · simpa [Env.setVar] using hkv
  · simp [Env.setVar]
  · simpa [Env.setVar] using htpv
  · simpa [Env.setVar] using haccv
  · simpa [Env.setVar, Tbl] using hTV
  · simpa [Env.setVar] using hTab

theorem head2_spec (hB : Bnd B I P n S C dl x) (k : ℕ) (hk : k < n) :
    Spec B (JA1 I P n S C ord dl nc x k) (.assign "t" (.get "dl" (V "k")))
      (fun _ σ' => JA2 I P n S C ord dl nc x k σ') 3 := by
  intro σ ⟨hctx, hkv, hjb, htpv, haccv, T, hTV, hTab⟩
  have hkB : k < B := by have := hB.nB; omega
  have hdB : dl k < B := by have := hB.dlB k hk; omega
  refine ⟨σ.setVar "t" (dl k),
    (Run.assign (evalB_getvar hkB hdB hkv (lt_of_lt_of_le hk hctx.lenDl)
      (hctx.dlA k hk))).mono (by norm_num [Expr.size]),
    ⟨?_, ?_, ?_, ?_, ?_, T, ?_, ?_⟩, ?_⟩
  · exact hctx.congr (fun y hy => by
        simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Env.setVar])
      (fun a _ => by simp [Env.setVar])
      (by simpa [Env.setVar] using hctx.lenV) (by simpa [Env.setVar] using hctx.lenV2)
      (by simpa [Env.setVar] using hctx.lenVt)
  · simpa [Env.setVar] using hkv
  · simpa [Env.setVar] using hjb
  · simpa [Env.setVar] using htpv
  · simpa [Env.setVar] using haccv
  · simpa [Env.setVar, Tbl] using hTV
  · simpa [Env.setVar] using hTab
  · simp [Env.setVar]

/-- **Closing a block.** If the job in hand starts a block, the block just finished is
added to the running total and the table is reset; otherwise nothing happens. -/
theorem cutBlock_spec (hO : Order I P n ord dl nc) (hB : Bnd B I P n S C dl x) (k : ℕ)
    (hk : k < n) :
    Spec B (JA2 I P n S C ord dl nc x k)
      (.ite (.eq (.get "nc" (V "k")) (lit 1)) (.seq closeBlock clearLoop) .skip)
      (fun _ σ' => JA3 I P n S C ord dl nc x k σ') (36 * S + 37) := by
  have hSpos : 0 < S := by rw [hB.size]; exact Nat.pow_pos (by omega)
  have hB1 : 1 < B := by have := hB.sB; omega
  have hkB : k < B := by have := hB.nB; omega
  refine (Spec.ite (b := .eq (.get "nc" (V "k")) (lit 1)) (K := 36 * S + 32) ?_ ?_ ?_).mono
    (by norm_num [Cond.size, Expr.size]; omega)
  · rintro σ ⟨⟨hctx, hkv, -, -, -, -⟩, -⟩
    exact ⟨nc k, nc_cond hctx hkv hk hkB hB1⟩
  · -- the job starts a block
    rintro σ ⟨⟨⟨hctx, hkv, hjb, htpv, haccv, T, hTV, hTab⟩, htv⟩, hbt⟩
    have hnck : nc k = true := by
      have hc := nc_cond hctx hkv hk hkB hB1
      rw [hc] at hbt; simpa using hbt
    obtain ⟨σ3, hrun3, ⟨⟨bst, hub, hat, hacc3⟩, hTV3, hS3, hcap3, hacc3le⟩, hfv3, hfa3, -, -⟩ :=
      (closeBlock_spec (B := B) S C T hB.sB (fun c _ => hTab.cap c) hB.cB).frame
        σ ⟨hctx.varS, hTV, hctx.varcap, by rw [haccv]; exact min_le_right _ _⟩
    have hbst : bst = min (optimumOn I (seg ord (cut nc k) k).toFinset) C + 1 := by
      refine tab_best (I := I) (P := P) hO.pmax hTab
        (seg_ord hO (le_of_lt hk) (cut_le nc k) (fun j h1 h2 => cut_gap nc k j h1 h2))
        (seg_nodup hO (le_of_lt hk)) (fun c hc => hub c (by rw [hB.size]; exact hc)) ?_
      rcases hat with h0 | ⟨c, hc, hTc⟩
      · exact Or.inl h0
      · exact Or.inr ⟨c, by rw [← hB.size]; exact hc, hTc⟩
    have hacc3' : σ3.vars "acc" = min (optimumOn I (seg ord 0 k).toFinset) C := by
      rw [hacc3, haccv, hbst, optimumOn_split' hO (le_of_lt hk)]
      exact min_add_min _ _ _
    obtain ⟨σ4, hrun4, ⟨hTV4, hS4, htp4⟩, hfv4, hfa4, -, -⟩ :=
      (clearLoop_spec (B := B) S hB.sB hSpos hB1).frame σ3 ⟨hS3, hTV3.1⟩
    have hV2 : σ4.arrs "V2" = σ.arrs "V2" := by
      rw [hfa4 _ (notMemA_clearLoop (by decide)), hfa3 _ (notMemA_closeBlock _)]
    have hVt : σ4.arrs "Vt" = σ.arrs "Vt" := by
      rw [hfa4 _ (notMemA_clearLoop (by decide)), hfa3 _ (notMemA_closeBlock _)]
    have hcut : cut nc (k + 1) = k := cut_succ_true hnck
    refine ⟨σ4, (hrun3.seq hrun4).mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (fun c => if c = 0 then 1 else 0), hTV4, ?_⟩
    · refine hctx.congr (fun y hy => ?_) (fun a ha => ?_) hTV4.1
        (by rw [hV2]; exact hctx.lenV2) (by rw [hVt]; exact hctx.lenVt)
      · simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          rw [hfv4 _ (notMem_clearLoop (by decide)), hfv3 _ (notMem_closeBlock (by decide))]
      · simp only [ctxArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl|rfl <;>
          rw [hfa4 _ (notMemA_clearLoop (by decide)), hfa3 _ (notMemA_closeBlock _)]
    · rw [hfv4 _ (notMem_clearLoop (by decide)), hfv3 _ (notMem_closeBlock (by decide))]
      exact hkv
    · rw [hfv4 _ (notMem_clearLoop (by decide)), hfv3 _ (notMem_closeBlock (by decide))]
      exact hjb
    · rw [hfv4 _ (notMem_clearLoop (by decide)), hfv3 _ (notMem_closeBlock (by decide))]
      exact htv
    · rw [hfv4 _ (notMem_clearLoop (by decide)), hacc3', hcut]
    · rw [htp4, hcut, seg_self]
      simp [refOf]
    · rw [htp4]; exact Nat.zero_le _
    · rw [htp4, hcut, seg_self]
      exact tab_init C
  · -- the job continues the block
    rintro σ ⟨⟨⟨hctx, hkv, hjb, htpv, haccv, T, hTV, hTab⟩, htv⟩, hbf⟩
    have hnck : nc k = false := by
      have hc := nc_cond hctx hkv hk hkB hB1
      rw [hc] at hbf; simpa using hbf
    have hcut : cut nc (k + 1) = cut nc k := cut_succ_false hnck
    refine ⟨σ, Run.skip.mono (by omega), hctx, hkv, hjb, htv, ?_, ?_, ?_, T, hTV, ?_⟩
    · rw [hcut]; exact haccv
    · rw [hcut, refOf_seg hO (le_of_lt hk) (cut_le nc k), htpv]
      split
      · exact Nat.zero_le _
      · rename_i hne
        have hk0 : k ≠ 0 := by rintro rfl; exact hne (by simp [cut])
        rw [if_neg hk0]
    · exact tp_le hO hk (σ.vars "tp") htpv hnck
    · rw [hcut]; exact hTab

theorem delStep_spec (hB : Bnd B I P n S C dl x) (k : ℕ) (hk : k < n) :
    Spec B (JA3 I P n S C ord dl nc x k) (.assign "del" (sub (V "t") (V "tp")))
      (fun _ σ' => JA4 I P n S C ord dl nc x k σ') 4 := by
  rintro σ ⟨hctx, hkv, hjb, htv, haccv, href, htple, T, hTV, hTab⟩
  have hdB : dl k < B := by have := hB.dlB k hk; omega
  have heval : (sub (V "t") (V "tp")).evalB B σ = some (dl k - σ.vars "tp") := by
    simp only [Expr.evalB, htv, fit_self hdB, fit_self (show σ.vars "tp" < B by omega),
      Option.bind_some, Bop.apply_sub]
    exact fit_self (by omega)
  refine ⟨σ.setVar "del" (dl k - σ.vars "tp"),
    (Run.assign heval).mono (by norm_num [Expr.size]),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, T, ?_, ?_⟩, ?_⟩
  · exact hctx.congr (fun y hy => by
        simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Env.setVar])
      (fun a _ => by simp [Env.setVar])
      (by simpa [Env.setVar] using hctx.lenV) (by simpa [Env.setVar] using hctx.lenV2)
      (by simpa [Env.setVar] using hctx.lenVt)
  · simpa [Env.setVar] using hkv
  · simpa [Env.setVar] using hjb
  · simpa [Env.setVar] using htv
  · simpa [Env.setVar] using haccv
  · simpa [Env.setVar] using href
  · simpa [Env.setVar] using htple
  · simpa [Env.setVar, Tbl] using hTV
  · simpa [Env.setVar] using hTab
  · simp [Env.setVar]

/-- **Letting time run** to the job's deadline. -/
theorem commitStep_spec (hB : Bnd B I P n S C dl x) (k : ℕ) (hk : k < n) :
    Spec B (JA4 I P n S C ord dl nc x k) commitLoop
      (fun _ σ' => JA5 I P n S C ord dl nc x k σ') ((44 * I.machines + 88) * S + 18) := by
  rintro σ ⟨⟨hctx, hkv, hjb, htv, haccv, href, htple, T, hTV, hTab⟩, hdel⟩
  have hSle : (P + 1) ^ I.machines ≤ S := le_of_eq hB.size.symm
  have hVeq : ∀ c, (σ.arrs "V").getD c 0 = T c := by
    intro c
    by_cases hc : c < S
    · exact hTV.2 c hc
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hTV.1]; omega)]
      simp only [Option.getD_none]
      exact (hTab.out c (by rw [← hB.size]; omega)).symm
  have hVfun : (fun c => (σ.arrs "V").getD c 0) = T := funext hVeq
  have hdlB := hB.dlB k hk
  obtain ⟨σ6, hrun6, ⟨hTV6, hTV26, hS6⟩, hfv6, hfa6, -, -⟩ :=
    (commitLoop_specG (B := B) I.machines P S (C + 1) hSle hB.mB
      (by have := hB.cB; omega)).frame σ
      ⟨hctx.varS, hctx.varm, hctx.varP, by rw [hdel]; omega, hctx.pw, hctx.lenV,
        fun c => by rw [hVeq c]; exact hTab.cap c, hctx.lenVt, hctx.lenV2⟩
  rw [hVfun, hdel] at hTV6 hTV26
  have hVtlen : (σ6.arrs "Vt").length = S := by
    rw [run_arrs_length hrun6 "Vt"]; exact hctx.lenVt
  have hTab6 : Tab (I := I) (P := P) C (seg ord (cut nc (k + 1)) k) (dl k)
      (pushed P I.machines (dl k - σ.vars "tp") T S) := by
    rw [hB.size]
    exact tab_shift hTab href htple
  refine ⟨σ6, hrun6, ?_, ?_, ?_, ?_, ?_, _, hTV6, hTV26, hTab6⟩
  · refine hctx.congr (fun y hy => ?_) (fun a ha => ?_) hTV6.1 hTV26.1 hVtlen
    · simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        exact hfv6 _ (notMem_commitLoop (by decide))
    · simp only [ctxArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl <;>
        exact hfa6 _ (notMemA_commitLoop (by decide))
  · rw [hfv6 _ (notMem_commitLoop (by decide))]; exact hkv
  · rw [hfv6 _ (notMem_commitLoop (by decide))]; exact hjb
  · rw [hfv6 _ (notMem_commitLoop (by decide))]; exact htv
  · rw [hfv6 _ (notMem_commitLoop (by decide))]; exact haccv

theorem tpStep_spec (hB : Bnd B I P n S C dl x) (k : ℕ) (hk : k < n) :
    Spec B (JA5 I P n S C ord dl nc x k) (.assign "tp" (V "t"))
      (fun _ σ' => JDone I P n S C ord dl nc x k σ') 2 := by
  rintro σ ⟨hctx, hkv, hjb, htv, haccv, T, hTV, hTV2, hTab⟩
  have hdB : dl k < B := by have := hB.dlB k hk; omega
  have heval : (V "t").evalB B σ = some (dl k) := by
    simp only [Expr.evalB, htv]; exact fit_self hdB
  refine ⟨σ.setVar "tp" (dl k), (Run.assign heval).mono (by norm_num [Expr.size]),
    ⟨?_, ?_, ?_, ?_, ?_, T, ?_, ?_, hTab⟩, ?_⟩
  · exact hctx.congr (fun y hy => by
        simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Env.setVar])
      (fun a _ => by simp [Env.setVar])
      (by simpa [Env.setVar] using hctx.lenV) (by simpa [Env.setVar] using hctx.lenV2)
      (by simpa [Env.setVar] using hctx.lenVt)
  · simpa [Env.setVar] using hkv
  · simpa [Env.setVar] using hjb
  · simpa [Env.setVar] using htv
  · simpa [Env.setVar] using haccv
  · simpa [Env.setVar, Tbl] using hTV
  · simpa [Env.setVar, Tbl] using hTV2
  · simp [Env.setVar]

/-- **Setting the table up for one job.** -/
theorem startJob_spec (hO : Order I P n ord dl nc) (hB : Bnd B I P n S C dl x) (k : ℕ)
    (hk : k < n) :
    Spec B (fun σ => LInv I P n S C ord dl nc x σ ∧ σ.vars "k" = k) startJob
      (fun _ σ' => JDone I P n S C ord dl nc x k σ')
      ((44 * I.machines + 124) * S + 67) := by
  have h6 := ((delStep_spec (B := B) (ord := ord) (nc := nc) hB k hk).seq
      ((commitStep_spec (B := B) (ord := ord) (nc := nc) hB k hk).seq
        (tpStep_spec (B := B) (ord := ord) (nc := nc) hB k hk)
        (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
      (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
  have h5 := (cutBlock_spec (B := B) hO hB k hk).seq h6 (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
  have h4 := (head2_spec (B := B) (ord := ord) (nc := nc) hB k hk).seq h5 (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
  exact ((head1_spec (B := B) hO hB k hk).seq h4 (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h)).mono (le_of_eq (by ring))

/-! ### Reading the job in hand off the word -/

/-- What the sweep needs to know about the word it was handed. -/
structure Enc (I : Instance) (x : List ℕ) : Prop where
  jc : jobCount x = I.jobs
  shape : 3 + 4 * I.jobs + offset x I.jobs ≤ x.length
  proc_eq : ∀ j : Fin I.jobs, proc x j = I.p j
  due_eq : ∀ j : Fin I.jobs, due x j = I.d j
  wt_eq : ∀ j : Fin I.jobs, wt x j = I.w j
  off_zero : offset x 0 = 0
  off_mono : ∀ j < I.jobs, offset x j ≤ offset x (j + 1)
  target_lt : ∀ t < offset x I.jobs, target x t < I.machines
  eligible_iff : ∀ (j : Fin I.jobs) (i : Fin I.machines),
    i ∈ I.eligible j ↔ ∃ t, offset x j ≤ t ∧ t < offset x (j + 1) ∧ target x t = i

lemma Enc.off_mono' (h : Enc I x) : ∀ b, b ≤ I.jobs → ∀ a, a ≤ b →
    offset x a ≤ offset x b := by
  intro b
  induction b with
  | zero => intro _ a ha; rw [show a = 0 from by omega]
  | succ b ih =>
      intro hb a ha
      rcases Nat.eq_or_lt_of_le ha with rfl | hlt
      · exact le_refl _
      · exact le_trans (ih (by omega) a (by omega)) (h.off_mono b (by omega))

variable (I P n S C ord dl nc x) in
/-- After the job in hand has been read off the word. -/
def JData (k : ℕ) (σ : Env) : Prop :=
  JDone I P n S C ord dl nc x k σ ∧ σ.vars "o1" = offset x (ord k).val ∧
    σ.vars "pj" = I.p (ord k) ∧ σ.vars "wj" = I.w (ord k) ∧
    σ.vars "elen" = offset x ((ord k).val + 1) - offset x (ord k).val

theorem jobData_spec (hO : Order I P n ord dl nc) (hB : Bnd B I P n S C dl x)
    (hEn : Enc I x) (k : ℕ) (hk : k < n) :
    Spec B (JDone I P n S C ord dl nc x k) jobData
      (fun _ σ' => JData I P n S C ord dl nc x k σ') 30 := by
  rintro σ ⟨⟨hctx, hkv, hjb, htv, haccv, T, hTV, hTV2, hTab⟩, htpv⟩
  have hjobs : (ord k).val < I.jobs := (ord k).isLt
  have hxl : 3 + 4 * I.jobs ≤ x.length := le_trans (by omega) hEn.shape
  have hlB := hB.lenx
  have hnj : n = I.jobs := hO.len
  have hb1 : offset x (ord k).val + 2 < B := by rw [offset, hEn.jc]; exact hB.xg _
  have hb2 : offset x ((ord k).val + 1) + 2 < B := by rw [offset, hEn.jc]; exact hB.xg _
  have hb3 : I.p (ord k) + 2 < B := by rw [← hEn.proc_eq (ord k), proc]; exact hB.xg _
  have hb4 : I.w (ord k) + 2 < B := by rw [← hEn.wt_eq (ord k), wt, hEn.jc]; exact hB.xg _
  have key : ∀ s : Env, s.arrs "a" = x → s.vars "O0" = 2 + 3 * I.jobs →
      s.vars "jb" = (ord k).val → s.vars "n" = n →
      (Expr.get "a" (add (V "O0") (V "jb"))).evalB B s = some (offset x (ord k).val) ∧
      (Expr.get "a" (add (add (V "O0") (V "jb")) (lit 1))).evalB B s
        = some (offset x ((ord k).val + 1)) ∧
      (Expr.get "a" (add (lit 2) (V "jb"))).evalB B s = some (I.p (ord k)) ∧
      (Expr.get "a" (add (add (lit 2) (mul (lit 2) (V "n"))) (V "jb"))).evalB B s
        = some (I.w (ord k)) := by
    intro s hsa hsO hsj hsn
    have hsl : (s.arrs "a").length = x.length := by rw [hsa]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine evalB_getE (evalB_add (evalB_var (by rw [hsO]; omega))
        (evalB_var (by rw [hsj]; omega)) (by rw [hsO, hsj]; omega)) (by omega)
        (by rw [hsO, hsj, hsl]; omega) ?_
      rw [hsO, hsj, hsa, offset, hEn.jc]
    · refine evalB_getE (evalB_add (evalB_add (evalB_var (by rw [hsO]; omega))
        (evalB_var (by rw [hsj]; omega)) (by rw [hsO, hsj]; omega))
        (evalB_lit (by omega)) (by rw [hsO, hsj]; omega)) (by omega)
        (by rw [hsO, hsj, hsl]; omega) ?_
      rw [hsO, hsj, hsa, offset, hEn.jc,
        show 2 + 3 * I.jobs + ((ord k).val + 1) = 2 + 3 * I.jobs + (ord k).val + 1 from by omega]
    · refine evalB_getE (evalB_add (evalB_lit (by omega))
        (evalB_var (by rw [hsj]; omega)) (by rw [hsj]; omega)) (by omega)
        (by rw [hsj, hsl]; omega) ?_
      rw [hsj, hsa, ← hEn.proc_eq (ord k), proc]
    · refine evalB_getE (evalB_add (evalB_add (evalB_lit (by omega))
        (evalB_mul (evalB_lit (by omega)) (evalB_var (by rw [hsn]; omega))
          (by rw [hsn]; omega)) (by rw [hsn]; omega))
        (evalB_var (by rw [hsj]; omega)) (by rw [hsn, hsj]; omega)) (by omega)
        (by rw [hsn, hsj, hsl]; omega) ?_
      rw [hsn, hsj, hsa, ← hEn.wt_eq (ord k), wt, hEn.jc, hnj]
  obtain ⟨e1, -, -, -⟩ := key σ hctx.arrA hctx.varO0 hjb hctx.varn
  obtain ⟨-, e2, -, -⟩ := key (σ.setVar "o1" (offset x (ord k).val))
    (by simp [Env.setVar, hctx.arrA]) (by simpa [Env.setVar] using hctx.varO0)
    (by simpa [Env.setVar] using hjb) (by simpa [Env.setVar] using hctx.varn)
  obtain ⟨-, -, e3, -⟩ := key (((σ.setVar "o1" (offset x (ord k).val)).setVar "o2"
      (offset x ((ord k).val + 1))).setVar "elen"
      (offset x ((ord k).val + 1) - offset x (ord k).val))
    (by simp [Env.setVar, hctx.arrA]) (by simpa [Env.setVar] using hctx.varO0)
    (by simpa [Env.setVar] using hjb) (by simpa [Env.setVar] using hctx.varn)
  obtain ⟨-, -, -, e4⟩ := key ((((σ.setVar "o1" (offset x (ord k).val)).setVar "o2"
      (offset x ((ord k).val + 1))).setVar "elen"
      (offset x ((ord k).val + 1) - offset x (ord k).val)).setVar "pj" (I.p (ord k)))
    (by simp [Env.setVar, hctx.arrA]) (by simpa [Env.setVar] using hctx.varO0)
    (by simpa [Env.setVar] using hjb) (by simpa [Env.setVar] using hctx.varn)
  have e5 : (sub (V "o2") (V "o1")).evalB B ((σ.setVar "o1" (offset x (ord k).val)).setVar "o2"
      (offset x ((ord k).val + 1)))
      = some (offset x ((ord k).val + 1) - offset x (ord k).val) := by
    refine evalB_sub (evalB_var ?_) (evalB_var ?_) ?_ |>.trans ?_
    · simp [Env.setVar]; omega
    · simp [Env.setVar]; omega
    · simp [Env.setVar]; omega
    · simp [Env.setVar]
  refine ⟨((((σ.setVar "o1" (offset x (ord k).val)).setVar "o2"
      (offset x ((ord k).val + 1))).setVar "elen"
      (offset x ((ord k).val + 1) - offset x (ord k).val)).setVar "pj"
      (I.p (ord k))).setVar "wj" (I.w (ord k)),
    ((Run.assign e1).seq ((Run.assign e2).seq ((Run.assign e5).seq
      ((Run.assign e3).seq (Run.assign e4))))).mono (by norm_num [Expr.size]),
    ⟨⟨?_, ?_, ?_, ?_, ?_, T, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact hctx.congr (fun y hy => by
        simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Env.setVar])
      (fun a _ => by simp [Env.setVar])
      (by simpa [Env.setVar] using hctx.lenV) (by simpa [Env.setVar] using hctx.lenV2)
      (by simpa [Env.setVar] using hctx.lenVt)
  · simpa [Env.setVar] using hkv
  · simpa [Env.setVar] using hjb
  · simpa [Env.setVar] using htv
  · simpa [Env.setVar] using haccv
  · simpa [Env.setVar, Tbl] using hTV
  · simpa [Env.setVar, Tbl] using hTV2
  · exact hTab
  · simpa [Env.setVar] using htpv
  · simp [Env.setVar]
  · simp [Env.setVar]
  · simp [Env.setVar]
  · simp [Env.setVar]

/-! ### Trying the job on its machines -/

/-- How many machines the word lists for job `j`. -/
def elenOf (x : List ℕ) (j : ℕ) : ℕ := offset x (j + 1) - offset x j

lemma eligList_mem (hEn : Enc I x) (j : Fin I.jobs) (i0 : Fin I.machines)
    (hx : ∀ t, t < offset x I.jobs → target x t < I.machines) (i : Fin I.machines) :
    i ∈ eligList I x j.val i0 hx (elenOf x j.val) ↔ i ∈ I.eligible j := by
  have hnext : offset x (j.val + 1) ≤ offset x I.jobs :=
    hEn.off_mono' I.jobs (le_refl _) _ j.isLt
  rw [hEn.eligible_iff j i]
  simp only [eligList, elenOf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨r, hr, hval⟩
    have hlt : offset x j.val + r < offset x I.jobs := by omega
    rw [dif_pos hlt] at hval
    exact ⟨offset x j.val + r, by omega, by omega, by rw [← hval]⟩
  · rintro ⟨t, h1, h2, h3⟩
    refine ⟨t - offset x j.val, by omega, ?_⟩
    have hlt : offset x j.val + (t - offset x j.val) < offset x I.jobs := by omega
    rw [dif_pos hlt]
    refine Fin.ext ?_
    simp only
    rw [show offset x j.val + (t - offset x j.val) = t from by omega]
    exact h3

variable (I P n S C ord dl nc x) in
/-- After the job has been tried on each machine it is eligible on. -/
def JElig (k : ℕ) (σ : Env) : Prop :=
  Ctx I P n S C ord dl nc x σ ∧ σ.vars "k" = k ∧ σ.vars "tp" = dl k ∧
    σ.vars "acc" = min (optimumOn I (seg ord 0 (cut nc (k + 1))).toFinset) C ∧
    ∃ T, Tbl "V2" S T σ ∧ (∀ c, T c ≤ C + 1) ∧
      Tab (I := I) (P := P) C (seg ord (cut nc (k + 1)) (k + 1)) (dl k) T

variable (I P n S C ord dl nc x) in
/-- …and the result has been installed as the current table. -/
def JTaken (k : ℕ) (σ : Env) : Prop :=
  Ctx I P n S C ord dl nc x σ ∧ σ.vars "k" = k ∧ σ.vars "tp" = dl k ∧
    σ.vars "acc" = min (optimumOn I (seg ord 0 (cut nc (k + 1))).toFinset) C ∧
    ∃ T, Tbl "V" S T σ ∧
      Tab (I := I) (P := P) C (seg ord (cut nc (k + 1)) (k + 1)) (dl k) T

theorem entryStep_spec (hO : Order I P n ord dl nc) (hB : Bnd B I P n S C dl x)
    (hEn : Enc I x) (i0 : Fin I.machines) (k : ℕ) (hk : k < n) :
    Spec B (JData I P n S C ord dl nc x k) entryLoop
      (fun _ σ' => JElig I P n S C ord dl nc x k σ')
      ((84 * S + 24) * elenOf x (ord k).val + 6) := by
  rintro σ ⟨⟨⟨hctx, hkv, hjb, htv, haccv, T, hTV, hTV2, hTab⟩, htpv⟩, ho1, hpj, hwj, helen⟩
  have hjobs : (ord k).val < I.jobs := (ord k).isLt
  have hnext : offset x ((ord k).val + 1) ≤ offset x I.jobs :=
    hEn.off_mono' I.jobs (le_refl _) _ hjobs
  have hb2 : offset x ((ord k).val + 1) + 2 < B := by rw [offset, hEn.jc]; exact hB.xg _
  have hb3 : I.p (ord k) + 2 < B := by rw [← hEn.proc_eq (ord k), proc]; exact hB.xg _
  have hb4 : C + I.w (ord k) + 3 < B := by
    rw [← hEn.wt_eq (ord k), wt, hEn.jc]; exact hB.wB _
  have hcap : ∀ c, T c ≤ C + 1 := hTab.cap
  obtain ⟨σ', hrun, ⟨hctx', hTV', hTV2', -⟩, hfv, hfa, -, -⟩ :=
    (entryLoop_spec (B := B) (n := n) (C := C) (ord := ord) (dl := dl) (nc := nc)
      (ord k).val (I.p (ord k)) (I.w (ord k)) (elenOf x (ord k).val) T i0
      hEn.target_lt (fun r hr => by simp only [elenOf] at hr; omega)
      hB.xg hB.sB hB.size hB.mB hB.pB (by omega) hb4 hcap hB.lenx
      (by simp only [elenOf]; omega) hEn.shape hEn.jc).frame σ
      ⟨hctx, hpj, hwj, hjb, ho1, helen, hTV, hTV2⟩
  have hEl : ∀ i, i ∈ eligList I x (ord k).val i0 hEn.target_lt (elenOf x (ord k).val) ↔
      i ∈ I.eligible (ord k) := eligList_mem hEn (ord k) i0 hEn.target_lt
  have hcut : cut nc (k + 1) ≤ k := cut_succ_le nc k
  have hdk : I.d (ord k) = dl k := (hO.dl_eq k hk).symm
  have hTabNew : Tab (I := I) (P := P) C (seg ord (cut nc (k + 1)) (k + 1)) (dl k)
      (foldRelax P I (I.p (ord k)) (I.w (ord k)) (C + 1) T
        (eligList I x (ord k).val i0 hEn.target_lt (elenOf x (ord k).val)) T) := by
    rw [seg_succ ord hcut, ← hdk]
    exact tab_job' (by rw [hdk]; exact hTab) _ hEl
  refine ⟨σ', hrun, hctx', ?_, ?_, ?_, _, hTV2', ?_, hTabNew⟩
  · rw [hfv _ (by simp [entryLoop, entryBody, relaxLoop, relaxBody, Com.wvars])]; exact hkv
  · rw [hfv _ (by simp [entryLoop, entryBody, relaxLoop, relaxBody, Com.wvars])]; exact htpv
  · rw [hfv _ (by simp [entryLoop, entryBody, relaxLoop, relaxBody, Com.wvars])]; exact haccv
  · exact fun c => foldRelax_le _ _ _ _ _ _ _ hcap (le_refl _) c

theorem takeStep_spec (hB : Bnd B I P n S C dl x) (k : ℕ) :
    Spec B (JElig I P n S C ord dl nc x k) takeLoop
      (fun _ σ' => JTaken I P n S C ord dl nc x k σ') (24 * S + 6) := by
  rintro σ ⟨hctx, hkv, htpv, haccv, T, hTV2, hTC, hTab⟩
  obtain ⟨σ', hrun, ⟨hTV', hTV2', -⟩, hfv, hfa, -, -⟩ :=
    (takeLoop_spec (B := B) S T hB.sB (fun c _ => by have := hTC c; have := hB.cB; omega)).frame
      σ ⟨hctx.varS, hTV2, hctx.lenV⟩
  have hV2 : σ'.arrs "V2" = σ.arrs "V2" := hfa _ (by simp [warrs_takeLoop])
  have hVt : σ'.arrs "Vt" = σ.arrs "Vt" := hfa _ (by simp [warrs_takeLoop])
  refine ⟨σ', hrun, ?_, ?_, ?_, ?_, T, hTV', hTab⟩
  · refine hctx.congr (fun y hy => ?_) (fun a ha => ?_) hTV'.1
      (by rw [hV2]; exact hctx.lenV2) (by rw [hVt]; exact hctx.lenVt)
    · simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hfv _ (by simp [wvars_takeLoop])
    · simp only [ctxArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl <;> exact hfa _ (by simp [warrs_takeLoop])
  · rw [hfv _ (by simp [wvars_takeLoop])]; exact hkv
  · rw [hfv _ (by simp [wvars_takeLoop])]; exact htpv
  · rw [hfv _ (by simp [wvars_takeLoop])]; exact haccv

theorem bumpStep_spec (hB : Bnd B I P n S C dl x) (k : ℕ) (hk : k < n) :
    Spec B (JTaken I P n S C ord dl nc x k) (bump "k")
      (fun _ σ' => LInv I P n S C ord dl nc x σ' ∧ σ'.vars "k" = k + 1) 4 := by
  rintro σ ⟨hctx, hkv, htpv, haccv, T, hTV, hTab⟩
  have hkB : k + 1 < B := by have := hB.nB; omega
  have heval : (add (V "k") (lit 1)).evalB B σ = some (k + 1) := by
    have h := evalB_add (evalB_var (B := B) (σ := σ) (y := "k") (by rw [hkv]; omega))
      (evalB_lit (show (1 : ℕ) < B by omega)) (by rw [hkv]; omega)
    rwa [hkv] at h
  have hk' : (σ.setVar "k" (k + 1)).vars "k" = k + 1 := by simp [Env.setVar]
  have htp' : (σ.setVar "k" (k + 1)).vars "tp" = dl k := by simpa [Env.setVar] using htpv
  have hacc' : (σ.setVar "k" (k + 1)).vars "acc"
      = min (optimumOn I (seg ord 0 (cut nc (k + 1))).toFinset) C := by
    simpa [Env.setVar] using haccv
  refine ⟨σ.setVar "k" (k + 1), (Run.assign heval).mono (by norm_num [Expr.size]),
    ⟨?_, ?_, ?_, ?_, T, ?_, ?_⟩, hk'⟩
  · exact hctx.congr (fun y hy => by
        simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Env.setVar])
      (fun a _ => by simp [Env.setVar])
      (by simpa [Env.setVar] using hctx.lenV) (by simpa [Env.setVar] using hctx.lenV2)
      (by simpa [Env.setVar] using hctx.lenVt)
  · rw [hk']; omega
  · rw [hk', htp']; simp
  · rw [hk', hacc']
  · simpa [Env.setVar, Tbl] using hTV
  · rw [hk', htp']; exact hTab

/-- **One turn of the sweep.** -/
theorem sweepBody_spec (hO : Order I P n ord dl nc) (hB : Bnd B I P n S C dl x)
    (hEn : Enc I x) (i0 : Fin I.machines) (k : ℕ) (hk : k < n) :
    Spec B (fun σ => LInv I P n S C ord dl nc x σ ∧ σ.vars "k" = k) sweepBody
      (fun _ σ' => LInv I P n S C ord dl nc x σ' ∧ σ'.vars "k" = k + 1)
      ((44 * I.machines + 148) * S + (84 * S + 24) * elenOf x (ord k).val + 113) := by
  have h4 := ((takeStep_spec (B := B) (ord := ord) (dl := dl) (nc := nc) hB k).seq
      (bumpStep_spec (B := B) (ord := ord) (nc := nc) hB k hk)
      (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
  have h3 := (entryStep_spec (B := B) hO hB hEn i0 k hk).seq h4
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  have h2 := (jobData_spec (B := B) hO hB hEn k hk).seq h3
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  exact ((startJob_spec (B := B) hO hB k hk).seq h2
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)).mono (le_of_eq (by ring))

/-! ### The sweep's outer loop -/

/-- What one turn costs, the loop's own test included. -/
def bodyCost (m S e : ℕ) : ℕ := (44 * m + 148) * S + (84 * S + 24) * e + 117

lemma sum_elen_range (hEn : Enc I x) : ∀ N, N ≤ I.jobs →
    ∑ i ∈ Finset.range N, elenOf x i = offset x N := by
  intro N
  induction N with
  | zero => intro _; simp [hEn.off_zero]
  | succ N ih =>
      intro hN
      rw [Finset.sum_range_succ, ih (by omega)]
      have h1 : offset x N ≤ offset x (N + 1) := hEn.off_mono N (by omega)
      simp only [elenOf]
      omega

lemma sum_elen_ord (hO : Order I P n ord dl nc) (hEn : Enc I x) :
    ∑ j ∈ Finset.range n, elenOf x (ord j).val = offset x I.jobs := by
  have hinj : ∀ a ∈ Finset.range n, ∀ b ∈ Finset.range n,
      (ord a).val = (ord b).val → a = b := by
    intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    exact hO.inj a b ha hb (Fin.ext hab)
  have himg : (Finset.range n).image (fun j => (ord j).val) = Finset.range I.jobs := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · simp only [Finset.mem_image, Finset.mem_range] at hy ⊢
      obtain ⟨j, -, rfl⟩ := hy
      exact (ord j).isLt
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_range, hO.len]
  rw [← sum_elen_range hEn I.jobs (le_refl _), ← himg, Finset.sum_image hinj]

/-- **The sweep's outer loop.** -/
theorem sweepWhile_spec (hO : Order I P n ord dl nc) (hB : Bnd B I P n S C dl x)
    (hEn : Enc I x) (i0 : Fin I.machines) :
    Spec B (LInv I P n S C ord dl nc x) (.while (.lt (V "k") (V "n")) sweepBody)
      (fun _ σ' => LInv I P n S C ord dl nc x σ' ∧ σ'.vars "k" = n)
      ((∑ j ∈ Finset.range n, bodyCost I.machines S (elenOf x (ord j).val)) + 4) := by
  have hnB := hB.nB
  have hsize : (Cond.lt (V "k") (V "n")).size = 3 := by simp [Cond.size, Expr.size]
  refine (Spec.while_potential (b := .lt (V "k") (V "n")) (c := sweepBody)
    (LInv I P n S C ord dl nc x)
    (fun σ => ∑ j ∈ Finset.Ico (σ.vars "k") n, bodyCost I.machines S (elenOf x (ord j).val))
    (fun σ hI => evalB_condLt_vars (by have := hI.2.1; omega) (by rw [hI.1.varn]; omega))
    ?_ (fun σ h => h) ?_).post ?_
  · intro σ hI hv
    have hlt : σ.vars "k" < n := by
      have h := lt_of_condLt_true hv
      rw [hI.1.varn] at h
      exact h
    obtain ⟨σ', hr, hI', hk'⟩ :=
      sweepBody_spec (B := B) hO hB hEn i0 (σ.vars "k") hlt σ ⟨hI, rfl⟩
    refine ⟨σ', _, hr, hI', ?_⟩
    rw [hk', Finset.sum_eq_sum_Ico_succ_bot hlt]
    simp only [bodyCost, hsize]
    omega
  · intro σ hI
    have hsub : Finset.Ico (σ.vars "k") n ⊆ Finset.range n := by
      intro y hy
      simp only [Finset.mem_Ico, Finset.mem_range] at hy ⊢
      omega
    have hle := Finset.sum_le_sum_of_subset (f := fun j =>
      bodyCost I.machines S (elenOf x (ord j).val)) hsub
    simp only [hsize]
    omega
  · rintro σ σ' - ⟨hI, hf⟩
    refine ⟨hI, ?_⟩
    have h1 := le_of_condLt_false hf
    rw [hI.1.varn] at h1
    have h2 := hI.2.1
    omega

/-- **The sweep.** -/
theorem sweepLoop_spec (hO : Order I P n ord dl nc) (hB : Bnd B I P n S C dl x)
    (hEn : Enc I x) (i0 : Fin I.machines) :
    Spec B (Ctx I P n S C ord dl nc x) sweepLoop
      (fun _ σ' => LInv I P n S C ord dl nc x σ' ∧ σ'.vars "k" = n)
      (16 * S + 20 + ∑ j ∈ Finset.range n, bodyCost I.machines S (elenOf x (ord j).val)) := by
  intro σ hctx
  have hSpos : 0 < S := by rw [hB.size]; exact Nat.pow_pos (by omega)
  have hB1 : 1 < B := by have := hB.sB; omega
  have e1 : (lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have e2 : (lit 0).evalB B (σ.setVar "acc" 0) = some 0 := evalB_lit (by omega)
  obtain ⟨σ3, hrun3, ⟨hTV3, hS3, htp3⟩, hfv3, hfa3, -, -⟩ :=
    (clearLoop_spec (B := B) S hB.sB hSpos hB1).frame ((σ.setVar "acc" 0).setVar "k" 0)
      ⟨by simpa [Env.setVar] using hctx.varS, by simpa [Env.setVar] using hctx.lenV⟩
  have hV2 : σ3.arrs "V2" = σ.arrs "V2" := by
    rw [hfa3 _ (notMemA_clearLoop (by decide))]; simp [Env.setVar]
  have hVt : σ3.arrs "Vt" = σ.arrs "Vt" := by
    rw [hfa3 _ (notMemA_clearLoop (by decide))]; simp [Env.setVar]
  have hk3 : σ3.vars "k" = 0 := by
    rw [hfv3 _ (notMem_clearLoop (by decide))]; simp [Env.setVar]
  have hacc3 : σ3.vars "acc" = 0 := by
    rw [hfv3 _ (notMem_clearLoop (by decide))]; simp [Env.setVar]
  have hctx3 : Ctx I P n S C ord dl nc x σ3 := by
    refine hctx.congr (fun y hy => ?_) (fun a ha => ?_) hTV3.1
      (by rw [hV2]; exact hctx.lenV2) (by rw [hVt]; exact hctx.lenVt)
    · simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (rw [hfv3 _ (notMem_clearLoop (by decide))]; simp [Env.setVar])
    · simp only [ctxArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl <;>
        (rw [hfa3 _ (notMemA_clearLoop (by decide))]; simp [Env.setVar])
  have hLInv : LInv I P n S C ord dl nc x σ3 := by
    refine ⟨hctx3, by rw [hk3]; omega, ?_, ?_, (fun c => if c = 0 then 1 else 0), hTV3, ?_⟩
    · rw [hk3, htp3]; simp
    · rw [hk3, hacc3]
      simp [cut, FreeDP.optimumOn_empty]
    · rw [hk3, htp3]
      simpa [cut] using tab_init (I := I) (P := P) C
  obtain ⟨σ4, hrun4, hfin⟩ := sweepWhile_spec (B := B) hO hB hEn i0 σ3 hLInv
  exact ⟨σ4, ((Run.assign e1).seq ((Run.assign e2).seq (hrun3.seq hrun4))).mono
    (by norm_num [Expr.size]; omega), hfin⟩

end Lax470956Proofs.SweepBody
