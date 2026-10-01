import Lax470956Proofs.EmitProg
import Lax470956Proofs.RamBridge
import Lax470956Proofs.Reduce
import Lax470956.Theorem2

/-!
The reduction of Theorem 2 as one program, on all words.

`Construction2.emit_computesInTime` is about well-formed formulas only: the program there
is handed a formula and writes the instance. A reduction is a function on every word, and
the machine that computes it has to decide, on its own, which case it is in. That decision
is what this file adds.

Deciding well-formedness is four checks, three of them immediate — the word has the right
length, it declares no more variables than it has literal slots, every literal names a
declared variable and carries one of four appearance indices. The fourth, that distinct
occurrences of one variable carry distinct appearance indices, is a disjointness condition
on `3C` pairs, and the obvious reading of it is quadratic. It is linear because the pairs
live in a small universe: an occurrence is a pair `(v, k)` with `v < V` and `k < 4`, so
bucketing it at `4v + k` in an array of `4V` cells and refusing a bucket that is already
taken decides the whole condition in one pass.

The program therefore reads its input into an array, runs the checks, and then either runs
the emitter of `EmitProg` — whose five passes are reused here unchanged, through the
specification each of them was given — or writes the fixed word a malformed input is sent
to.

# The Input Convention

The program is handed `|x| :: x` rather than `x`. It has to be: it reads a word of unknown
length, and nothing in the machine tells it where the input ends, so the length has to be
on the tape. This is the convention of `Lax759944.RamPolytime`, which is where the
statement is going.
-/

namespace Lax470956Proofs.Checker

open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer
open Lax470956.Exact34Encoding Lax470956.Construction2
open Lax470956Proofs.EmitProg

/-! ### Well-formedness as a condition on literal slots

The `3C` literal slots of a formula are numbered consecutively, slot `3c + h` being
literal `h` of clause `c`. The two conditions the pass checks are stated on slots, which
is the form the loop invariant needs; `good_iff` is the translation back. -/

/-- The variable named by literal slot `i`. -/
def vAt (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + 3 * i) 0

/-- The appearance index carried by literal slot `i`. -/
def kAt (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + 3 * i + 2) 0

lemma vAt_eq (x : List ℕ) (c h : ℕ) : vAt x (3 * c + h) = litVar x c h := by
  have he : 2 + 3 * (3 * c + h) = 2 + 9 * c + 3 * h := by omega
  rw [vAt, litVar, he]

lemma kAt_eq (x : List ℕ) (c h : ℕ) : kAt x (3 * c + h) = litApp x c h := by
  have he : 2 + 3 * (3 * c + h) + 2 = 2 + 9 * c + 3 * h + 2 := by omega
  rw [kAt, litApp, he]

/-- The first `n` literal slots are in range and pairwise distinct as occurrences. -/
def Good (x : List ℕ) (n : ℕ) : Prop :=
  (∀ i < n, vAt x i < varCount x ∧ kAt x i < 4) ∧
    (∀ i < n, ∀ i' < n, vAt x i = vAt x i' → kAt x i = kAt x i' → i = i')

/-- Fewer slots is a weaker condition, so one counter suffices: once the pass
has rejected, nothing later can rescue the word. -/
lemma Good.mono {x : List ℕ} {m n : ℕ} (h : Good x n) (hmn : m ≤ n) : Good x m :=
  ⟨fun i hi => h.1 i (lt_of_lt_of_le hi hmn),
   fun i hi i' hi' => h.2 i (lt_of_lt_of_le hi hmn) i' (lt_of_lt_of_le hi' hmn)⟩

/-- **The pass decides three of the five conditions.** -/
lemma good_iff (x : List ℕ) :
    Good x (3 * clauseCount x) ↔
      ((∀ c < clauseCount x, ∀ h < 3, litVar x c h < varCount x) ∧
       (∀ c < clauseCount x, ∀ h < 3, litApp x c h < 4) ∧
       (∀ c < clauseCount x, ∀ h < 3, ∀ c' < clauseCount x, ∀ h' < 3,
         litVar x c h = litVar x c' h' → litApp x c h = litApp x c' h' → c = c' ∧ h = h')) := by
  constructor
  · rintro ⟨hrange, hinj⟩
    refine ⟨fun c hc h hh => ?_, fun c hc h hh => ?_, fun c hc h hh c' hc' h' hh' hv hk => ?_⟩
    · rw [← vAt_eq]; exact (hrange (3 * c + h) (by omega)).1
    · rw [← kAt_eq]; exact (hrange (3 * c + h) (by omega)).2
    · have := hinj (3 * c + h) (by omega) (3 * c' + h') (by omega)
        (by rw [vAt_eq, vAt_eq]; exact hv) (by rw [kAt_eq, kAt_eq]; exact hk)
      omega
  · rintro ⟨hv, hk, hinj⟩
    refine ⟨fun i hi => ?_, fun i hi i' hi' he hf => ?_⟩
    · have h3 : i = 3 * (i / 3) + i % 3 := by omega
      rw [h3, vAt_eq, kAt_eq]
      exact ⟨hv _ (by omega) _ (by omega), hk _ (by omega) _ (by omega)⟩
    · have h3 : i = 3 * (i / 3) + i % 3 := by omega
      have h3' : i' = 3 * (i' / 3) + i' % 3 := by omega
      rw [h3, vAt_eq] at he; rw [h3', vAt_eq] at he
      rw [h3, kAt_eq] at hf; rw [h3', kAt_eq] at hf
      have := hinj _ (show i / 3 < clauseCount x by omega) _ (show i % 3 < 3 by omega)
        _ (show i' / 3 < clauseCount x by omega) _ (show i' % 3 < 3 by omega) he hf
      omega

/-- **The five conditions, as the pass sees them.** -/
lemma wellFormed_iff (x : List ℕ) :
    WellFormed x ↔
      (x.length = 2 + 9 * clauseCount x ∧ varCount x ≤ 3 * clauseCount x ∧
        Good x (3 * clauseCount x)) := by
  rw [good_iff]
  constructor
  · intro h
    exact ⟨h.length_eq, h.var_le, h.var_lt, h.app_lt, h.app_inj⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h3, h4, h2, h5⟩

/-! ### The program

Three arrays: `w` holds the input, `a` the clause block, which the passes of
`EmitProg` read, so they are reused here unchanged, and `seen` one cell per
possible occurrence `(v, k)`.
-/

private abbrev sub (e f : Expr) : Expr := .bin .sub e f
private abbrev mul (e f : Expr) : Expr := .bin .mul e f
private abbrev add (e f : Expr) : Expr := .bin .add e f

/-- Copy one entry of the input into the array that holds it. -/
def wBody : Com :=
  .seq (.read "v")
    (.seq (.store "w" (.var "t") (.var "v"))
      (.assign "t" (add (.var "t") (.lit 1))))

/-- Read the whole input, whose length the first entry announced. -/
def wLoop : Com :=
  .seq (.assign "t" (.lit 0)) (.while (.lt (.var "t") (.var "len")) wBody)

/-- Copy one entry of the clause block. -/
def aBody : Com :=
  .seq (.store "a" (.var "q") (.get "w" (add (.var "q") (.lit 2))))
    (.assign "q" (add (.var "q") (.lit 1)))

/-- Split the header off: what remains is the array the emitter's passes read. -/
def aLoop : Com :=
  .seq (.assign "q" (.lit 0)) (.while (.lt (.var "q") (.var "T2")) aBody)

/-- Read the variable and the appearance index of literal slot `i`. -/
def markRead : Com :=
  .seq (.assign "u" (.get "a" (mul (.lit 3) (.var "i"))))
       (.assign "e" (.get "a" (add (mul (.lit 3) (.var "i")) (.lit 2))))

/-- Reject. -/
def markFail : Com := .assign "ok" (.lit 0)

/-- Claim the bucket of an occurrence, or reject because it is taken. -/
def markTry : Com :=
  .seq (.assign "m" (add (mul (.lit 4) (.var "u")) (.var "e")))
  (.seq (.assign "z" (.get "seen" (.var "m")))
    (.ite (.eq (.var "z") (.lit 1)) markFail (.store "seen" (.var "m") (.lit 1))))

/-- One literal slot: its variable and its appearance index have to be in range, and the
occurrence they make has to be one no earlier slot made. -/
def markCore : Com :=
  .ite (.lt (.var "u") (.var "V"))
    (.ite (.lt (.var "e") (.lit 4)) markTry markFail)
    markFail

/-- One literal slot, and on to the next. -/
def markBody : Com :=
  .seq markRead (.seq markCore (.assign "i" (add (.var "i") (.lit 1))))

/-- The one pass that decides the disjointness of the occurrences. -/
def markLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "T3")) markBody)

/-- Read the input and split off its header. -/
def checkRead : Com :=
  .seq (.read "len")
  (.seq wLoop
  (.seq (.assign "V" (.get "w" (.lit 0)))
  (.seq (.assign "C" (.get "w" (.lit 1)))
  (.seq (.assign "T2" (sub (.var "len") (.lit 2)))
        aLoop))))

/-- The three immediate checks: the word has the length its header announces, and it
declares no more variables than it has literal slots. -/
def checkTests : Com :=
  .seq (.assign "ok" (.lit 1))
  (.seq (.ite (.eq (.var "len") (add (.lit 2) (mul (.lit 9) (.var "C"))))
          .skip (.assign "ok" (.lit 0)))
  (.seq (.ite (.lt (mul (.lit 3) (.var "C")) (.var "V")) (.assign "ok" (.lit 0)) .skip)
        (.assign "T3" (mul (.lit 3) (.var "C")))))

/-- Read the input, split off its header, and run the three immediate checks. -/
def checkHead : Com := .seq checkRead checkTests

/-- The fourth check, which is worth running only if the first three passed: the array of
buckets is sized by the header, and the loop reads the clause block by it. -/
def checkBody : Com := .ite (.eq (.var "ok") (.lit 1)) markLoop .skip

/-- **The decision.** -/
def checker : Com := .seq checkHead checkBody

/-- The emitter of `EmitProg`, started from the scalars and the array the checker leaves
behind rather than from the input tape. -/
def emitPart : Com :=
  .seq (.assign "L" (mul (.lit 9) (.var "C")))
  (.seq (.assign "n" (add (.var "V") (mul (.lit 9) (.var "C"))))
  (.seq (.assign "M" (add (mul (.lit 2) (.var "V")) (mul (.lit 3) (.var "C"))))
  (.seq (.assign "N" (add (.var "n") (.lit 1)))
  (.seq (.write (.var "n"))
  (.seq (.write (.var "M"))
  (.seq (jobLoop procBody "n")
  (.seq (jobLoop dueBody "n")
  (.seq (jobLoop wtBody "n")
  (.seq (jobLoop offBody "N")
        (jobLoop tgtBody "n"))))))))))

/-- The word a malformed input is sent to. -/
def noPart : Com :=
  .seq (.write (.lit 1))
  (.seq (.write (.lit 0))
  (.seq (.write (.lit 1))
  (.seq (.write (.lit 1))
  (.seq (.write (.lit 1))
  (.seq (.write (.lit 0))
        (.write (.lit 0)))))))

/-- Emit, or divert. -/
def tailCom : Com := .ite (.eq (.var "ok") (.lit 1)) emitPart noPart

/-- **The reduction, on every word.** -/
def com : Com := .seq checker tailCom

/-- Twenty-eight scalars, three arrays, eight temporaries. -/
def layout : Layout :=
  ⟨["V", "C", "L", "n", "M", "N", "t", "j", "v", "q", "c", "h", "s", "p", "k", "d",
    "b", "r", "g", "len", "ok", "i", "T2", "T3", "u", "e", "m", "z"],
   ["w", "a", "seen"], 8⟩

theorem com_ok : Com.Ok layout com := by
  simp [com, checker, checkHead, checkRead, checkTests, checkBody, wLoop, wBody, aLoop, aBody, markLoop, markBody, markRead, markCore, markTry, markFail, tailCom, emitPart, noPart,
    jobLoop, procBody, procDispatch, dueBody, dueDispatch, wtBody, offBody, tgtBody,
    tgtDispatch, decode, bumpJ, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by simp [Layout.const]

/-! ### The value bound

The bound is the emitter's own: everything the checker forms is an entry of the input, a
count of them, or a bucket index `4v + k`, and the bucket index is four times an entry. -/

lemma getD_lt_bnd (x : List ℕ) (i : ℕ) : x.getD i 0 < bnd x := by
  rcases Nat.lt_or_ge i x.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact entry_lt_bnd x (List.getElem_mem h)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]
    simp only [bnd]; omega

lemma varCount_lt_bnd (x : List ℕ) : varCount x < bnd x := getD_lt_bnd x 0
lemma clauseCount_lt_bnd (x : List ℕ) : clauseCount x < bnd x := getD_lt_bnd x 1

lemma length_lt_bnd (x : List ℕ) : x.length + 1 < bnd x := by simp only [bnd]; omega

lemma four_getD_lt_bnd (x : List ℕ) (i : ℕ) : 4 * x.getD i 0 + 3 < bnd x := by
  have h := getD_lt_bnd x i
  have h0 : x.getD i 0 ≤ x.foldr max 0 := by
    rcases Nat.lt_or_ge i x.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]
      exact Lax470956Proofs.Pmax.le_foldr_max (List.getElem_mem hi)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
      omega
  simp only [bnd]; omega

lemma nine_clauseCount_lt_bnd (x : List ℕ) : 2 + 9 * clauseCount x < bnd x := by
  have h0 : clauseCount x ≤ x.foldr max 0 := by
    rcases Nat.lt_or_ge 1 x.length with hi | hi
    · rw [clauseCount, List.getD_eq_getElem _ _ hi]
      exact Lax470956Proofs.Pmax.le_foldr_max (List.getElem_mem hi)
    · rw [clauseCount, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
      omega
  simp only [bnd]; omega

/-! ### Reading the Clause Block -/


lemma drop2_getD (x : List ℕ) (i : ℕ) : (x.drop 2).getD i 0 = x.getD (2 + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

/-! ### Reading the input

The program is handed the length of its input and then the input. It copies the whole of
it into an array, because every later pass reads it more than once and the tape is read
once. -/

/-- The state of the loop that reads the input. -/
def WInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "len" = x.length ∧ σ.vars "t" ≤ x.length ∧
    (σ.arrs "w").length = x.length + 2 ∧
    (∀ i < σ.vars "t", (σ.arrs "w").getD i 0 = x.getD i 0) ∧
    (∀ i, x.length ≤ i → (σ.arrs "w").getD i 0 = 0) ∧
    (σ.arrs "a").length = x.length - 2 ∧
    σ.arrs "seen" = List.replicate (12 * x.length + 12) 0 ∧
    σ.inp = x.drop (σ.vars "t") ∧ σ.out = []

theorem wBody_spec (x : List ℕ) :
    Spec (bnd x) (fun σ => WInv x σ ∧ σ.vars "t" < x.length) wBody
      (fun σ σ' => WInv x σ' ∧ σ'.vars "t" = σ.vars "t" + 1) 8 := by
  refine Spec.pre (P := fun σ => WInv x σ ∧ σ.vars "t" < x.length ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < bnd x ∧ σ.vars "t" < (σ.arrs "w").length ∧
      σ.vars "t" + 1 < bnd x) ?_ ?_
  · run_vcg
    · obtain ⟨hlen, hle, hwlen, hcell, hzero, halen, hseen, hinp, hout⟩ := ‹WInv x σ›
      have htlt := ‹σ.vars "t" < x.length›
      have hidx : σ.vars "t" < (σ.arrs "w").length := by rw [hwlen]; omega
      simp only [WInv]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hlen
      · omega
      · exact hwlen
      · intro i hi
        rcases Nat.lt_or_ge i (σ.vars "t") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell i h
        · have hie : i = σ.vars "t" := by omega
          subst hie
          rw [hinp]
          simp [List.getElem?_set, hidx, List.head?_drop, List.getD_eq_getElem?_getD]
      · intro i hi
        rw [List.getElem?_set_ne (by omega)]
        simpa [List.getD_eq_getElem?_getD] using hzero i hi
      · exact halen
      · exact hseen
      · rw [hinp, List.tail_drop]
      · exact hout
    · simp only [Env.setVar, if_pos rfl]
      exact ‹σ.inp.headD 0 < bnd x›
  · rintro σ ⟨hI, ht⟩
    have hinp : σ.inp = x.drop (σ.vars "t") := hI.2.2.2.2.2.2.2.1
    have hne : σ.inp ≠ [] := by
      rw [hinp]
      intro hc
      have : ((x.drop (σ.vars "t"))).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop] at this
      omega
    refine ⟨hI, ht, hne, ?_, ?_, ?_⟩
    · have hsub : ∀ u ∈ σ.inp, u ∈ x := by
        intro u hu
        rw [hinp] at hu
        exact List.mem_of_mem_drop hu
      rcases hh : σ.inp with _ | ⟨u, rest⟩
      · exact absurd hh hne
      · exact entry_lt_bnd x (hsub u (by rw [hh]; exact List.mem_cons_self))
    · rw [hI.2.2.1]; omega
    · have := length_lt_bnd x; omega

theorem wLoop_spec (x : List ℕ) :
    Spec (bnd x) (fun σ => WInv x (σ.setVar "t" 0)) wLoop
      (fun _ σ' => WInv x σ' ∧ σ'.vars "t" = x.length) (12 * x.length + 6) :=
  Spec.forRangeZero "t" "len" (WInv x) x.length 8
    (by have := length_lt_bnd x; omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (wBody_spec x)

/-- When the read loop is done the array is the input, padded with the two cells that make
the header always readable. -/
theorem w_read (x : List ℕ) {σ : Env} (h : WInv x σ) (ht : σ.vars "t" = x.length)
    (i : ℕ) : (σ.arrs "w").getD i 0 = x.getD i 0 := by
  obtain ⟨-, -, -, hcell, hzero, -, -, -, -⟩ := h
  rcases Nat.lt_or_ge i x.length with hi | hi
  · exact hcell i (by omega)
  · rw [hzero i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

/-! ### Splitting Off the Header -/

/-- The state of the loop that copies the clause block. -/
def AInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "len" = x.length ∧ σ.vars "V" = varCount x ∧ σ.vars "C" = clauseCount x ∧
    σ.vars "T2" = x.length - 2 ∧ σ.vars "q" ≤ x.length - 2 ∧
    (σ.arrs "w").length = x.length + 2 ∧
    (∀ i, (σ.arrs "w").getD i 0 = x.getD i 0) ∧
    (σ.arrs "a").length = x.length - 2 ∧
    (∀ i < σ.vars "q", (σ.arrs "a").getD i 0 = (x.drop 2).getD i 0) ∧
    σ.arrs "seen" = List.replicate (12 * x.length + 12) 0 ∧
    σ.out = []

theorem aBody_spec (x : List ℕ) :
    Spec (bnd x) (fun σ => AInv x σ ∧ σ.vars "q" < x.length - 2) aBody
      (fun σ σ' => AInv x σ' ∧ σ'.vars "q" = σ.vars "q" + 1) 10 := by
  refine Spec.pre (P := fun σ => AInv x σ ∧ σ.vars "q" < x.length - 2 ∧
      σ.vars "q" + 2 < bnd x ∧ σ.vars "q" + 1 < bnd x ∧
      σ.vars "q" + 2 < (σ.arrs "w").length ∧
      (σ.arrs "w").getD (σ.vars "q" + 2) 0 < bnd x ∧
      σ.vars "q" < (σ.arrs "a").length) ?_ ?_
  · run_vcg
    obtain ⟨hlen, hV, hC, hT2, hle, hwlen, hw, halen, hcell, hseen, hout⟩ := ‹AInv x σ›
    have hqlt := ‹σ.vars "q" < x.length - 2›
    have hidx : σ.vars "q" < (σ.arrs "a").length := by rw [halen]; omega
    simp only [AInv]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
    · exact hlen
    · exact hV
    · exact hC
    · exact hT2
    · omega
    · exact hwlen
    · exact hw
    · exact halen
    · intro i hi
      rcases Nat.lt_or_ge i (σ.vars "q") with h | h
      · rw [List.getElem?_set_ne (by omega)]
        simpa [List.getD_eq_getElem?_getD] using hcell i h
      · have hie : i = σ.vars "q" := by omega
        subst hie
        have hcomm : σ.vars "q" + 2 = 2 + σ.vars "q" := by omega
        have h2 := hw (2 + σ.vars "q")
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at h2
        rw [hcomm, h2]
        simp [List.getElem?_set, hidx]
    · exact hseen
    · exact hout
  · rintro σ ⟨hI, hq⟩
    have hwlen : (σ.arrs "w").length = x.length + 2 := hI.2.2.2.2.2.1
    have halen : (σ.arrs "a").length = x.length - 2 := hI.2.2.2.2.2.2.2.1
    have hb := length_lt_bnd x
    exact ⟨hI, hq, by omega, by omega, by omega, by
      rw [hI.2.2.2.2.2.2.1]; exact getD_lt_bnd x _, by omega⟩

theorem aLoop_spec (x : List ℕ) :
    Spec (bnd x) (fun σ => AInv x (σ.setVar "q" 0)) aLoop
      (fun _ σ' => AInv x σ' ∧ σ'.vars "q" = x.length - 2) (14 * (x.length - 2) + 6) :=
  Spec.forRangeZero "q" "T2" (AInv x) (x.length - 2) 10
    (by have := length_lt_bnd x; omega)
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.2.1) (aBody_spec x)

/-- When the copy loop is done the array is the clause block that every pass of
the emitter reads. -/
theorem arr_a_eq (x : List ℕ) {σ : Env} (h : AInv x σ) (hq : σ.vars "q" = x.length - 2) :
    σ.arrs "a" = x.drop 2 := by
  obtain ⟨-, -, -, -, -, -, -, halen, hcell, -, -⟩ := h
  refine List.ext_getElem (by rw [halen, List.length_drop]) ?_
  intro i h1 h2
  have hi := hcell i (by rw [hq]; rw [halen] at h1; exact h1)
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at hi

/-! ### The bucketing argument

The pass keeps one bit per occurrence `(v, k)`, at `4v + k`, and the whole of
`app_inj` is that no bit is set twice. -/

/-- The bucket of literal slot `i`. -/
def key (x : List ℕ) (i : ℕ) : ℕ := 4 * vAt x i + kAt x i

lemma key_inj {x : List ℕ} {i i' : ℕ} (h : key x i = key x i')
    (hk : kAt x i < 4) (hk' : kAt x i' < 4) : vAt x i = vAt x i' ∧ kAt x i = kAt x i' := by
  simp only [key] at h; omega

/-- A slot out of range refutes the condition outright. -/
lemma not_good_succ (x : List ℕ) (n : ℕ) (hbad : ¬(vAt x n < varCount x ∧ kAt x n < 4)) :
    ¬ Good x (n + 1) := fun hg => hbad (hg.1 n (Nat.lt_succ_self n))

/-- A bucket already taken refutes it too. -/
lemma not_good_succ_dup (x : List ℕ) (n i' : ℕ) (hi' : i' < n) (hki : kAt x i' < 4)
    (hkn : kAt x n < 4) (hkey : key x i' = key x n) : ¬ Good x (n + 1) := by
  intro hg
  obtain ⟨h1, h2⟩ := key_inj hkey hki hkn
  have := hg.2 i' (by omega) n (by omega) h1 h2
  omega

/-- A slot in range whose bucket is free extends the condition by one. -/
lemma good_succ (x : List ℕ) (n : ℕ) (hg : Good x n) (hv : vAt x n < varCount x)
    (hk : kAt x n < 4) (hfresh : ∀ i' < n, key x i' ≠ key x n) : Good x (n + 1) := by
  refine ⟨fun i hi => ?_, fun i hi i' hi' hv' hk' => ?_⟩
  · rcases Nat.lt_or_ge i n with h | h
    · exact hg.1 i h
    · have hin : i = n := by omega
      subst hin; exact ⟨hv, hk⟩
  · rcases Nat.lt_or_ge i n with h | h <;> rcases Nat.lt_or_ge i' n with h' | h'
    · exact hg.2 i h i' h' hv' hk'
    · have hin : i' = n := by omega
      subst hin
      exact absurd (by simp only [key, hv', hk']) (hfresh i h)
    · have hin : i = n := by omega
      subst hin
      exact absurd (show key x i' = key x i by simp only [key, hv', hk']) (hfresh i' h')
    · omega

lemma getD_set_self (l : List ℕ) (m v : ℕ) (h : m < l.length) : (l.set m v).getD m 0 = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

lemma getD_set_ne (l : List ℕ) {m m' : ℕ} (h : m' ≠ m) (v : ℕ) :
    (l.set m v).getD m' 0 = l.getD m' 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set,
    if_neg (Ne.symm h)]

/-- Setting the bucket of slot `n` is exactly what the characterisation of the array
asks, one slot further on. -/
lemma seen_update {x : List ℕ} {l : List ℕ} {n m : ℕ}
    (hchar : ∀ m' < l.length, l.getD m' 0 = 1 ↔ ∃ i' < n, key x i' = m')
    (hm : m = key x n) (hmlt : m < l.length) :
    ∀ m' < (l.set m 1).length, (l.set m 1).getD m' 0 = 1 ↔ ∃ i' < n + 1, key x i' = m' := by
  intro m' hm'
  rw [List.length_set] at hm'
  by_cases he : m' = m
  · subst he
    rw [getD_set_self l m' 1 hmlt]
    exact ⟨fun _ => ⟨n, Nat.lt_succ_self n, hm.symm⟩, fun _ => rfl⟩
  · rw [getD_set_ne l he 1, hchar m' hm']
    constructor
    · rintro ⟨i', hi', hk⟩; exact ⟨i', by omega, hk⟩
    · rintro ⟨i', hi', hk⟩
      rcases Nat.lt_or_ge i' n with h | h
      · exact ⟨i', h, hk⟩
      · exact absurd (by rw [← hk, show i' = n by omega, ← hm]) he

/-! ### The Marking Pass -/

/-- What the pass has established about the first `n` slots. -/
def Tally (x : List ℕ) (n : ℕ) (σ : Env) : Prop :=
  (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1) ∧
    (σ.vars "ok" = 1 → Good x n ∧ ∀ m < (σ.arrs "seen").length,
      ((σ.arrs "seen").getD m 0 = 1 ↔ ∃ i' < n, key x i' = m)) ∧
    (σ.vars "ok" = 0 → ¬ Good x n)

/-- What the pass keeps fixed. It runs only when the header checks have passed, so the
two conditions on the header are part of it. -/
def Frame (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "V" = varCount x ∧ σ.vars "C" = clauseCount x ∧ σ.vars "T3" = 3 * clauseCount x ∧
    x.length = 2 + 9 * clauseCount x ∧ varCount x ≤ 3 * clauseCount x ∧
    σ.arrs "a" = x.drop 2 ∧ (σ.arrs "seen").length = 12 * x.length + 12 ∧
    (∀ m, (σ.arrs "seen").getD m 0 ≤ 1) ∧ σ.out = []

/-- The state of the marking pass. -/
def MInv (x : List ℕ) (σ : Env) : Prop :=
  Frame x σ ∧ σ.vars "i" ≤ 3 * clauseCount x ∧ Tally x (σ.vars "i") σ

lemma a_len (x : List ℕ) {σ : Env} (h : Frame x σ) :
    (σ.arrs "a").length = 9 * clauseCount x := by
  rw [h.2.2.2.2.2.1, List.length_drop, h.2.2.2.1]
  omega

lemma frame_congr (x : List ℕ) {σ σ' : Env} (h : Frame x σ)
    (hV : σ'.vars "V" = σ.vars "V") (hC : σ'.vars "C" = σ.vars "C")
    (hT3 : σ'.vars "T3" = σ.vars "T3") (ha : σ'.arrs "a" = σ.arrs "a")
    (hs : σ'.arrs "seen" = σ.arrs "seen") (ho : σ'.out = σ.out) : Frame x σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨hV.trans h1, hC.trans h2, hT3.trans h3, h4, h5, ha.trans h6,
    by rw [hs]; exact h7, by rw [hs]; exact h8, ho.trans h9⟩

lemma frame_mark (x : List ℕ) {σ σ' : Env} (h : Frame x σ) {m : ℕ}
    (hm : m < (σ.arrs "seen").length)
    (hV : σ'.vars "V" = σ.vars "V") (hC : σ'.vars "C" = σ.vars "C")
    (hT3 : σ'.vars "T3" = σ.vars "T3") (ha : σ'.arrs "a" = σ.arrs "a")
    (hs : σ'.arrs "seen" = (σ.arrs "seen").set m 1) (ho : σ'.out = σ.out) : Frame x σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨hV.trans h1, hC.trans h2, hT3.trans h3, h4, h5, ha.trans h6, ?_, ?_, ho.trans h9⟩
  · rw [hs, List.length_set]; exact h7
  · intro m'
    rw [hs]
    by_cases he : m' = m
    · subst he
      rw [getD_set_self _ _ _ hm]
    · rw [getD_set_ne _ he]; exact h8 m'

lemma tally_fail (x : List ℕ) {σ' : Env} {n : ℕ}
    (hok : σ'.vars "ok" = 0) (hbad : ¬ Good x (n + 1)) : Tally x (n + 1) σ' :=
  ⟨Or.inl hok, fun h1 => absurd (hok.symm.trans h1) (by omega), fun _ => hbad⟩

lemma tally_mark (x : List ℕ) {σ σ' : Env} {n : ℕ} (hT : Tally x n σ)
    (hok : σ'.vars "ok" = σ.vars "ok")
    (hs : σ'.arrs "seen" = (σ.arrs "seen").set (key x n) 1)
    (hmlt : key x n < (σ.arrs "seen").length)
    (hfree : (σ.arrs "seen").getD (key x n) 0 ≠ 1)
    (hv : vAt x n < varCount x) (hk : kAt x n < 4) : Tally x (n + 1) σ' := by
  refine ⟨by rw [hok]; exact hT.1, fun h1 => ?_, fun h0 => ?_⟩
  · obtain ⟨hgood, hchar⟩ := hT.2.1 (hok.symm.trans h1)
    have hfresh : ∀ i' < n, key x i' ≠ key x n := by
      intro i' hi' hkey
      exact hfree ((hchar _ hmlt).mpr ⟨i', hi', hkey⟩)
    refine ⟨good_succ x n hgood hv hk hfresh, ?_⟩
    rw [hs]
    exact seen_update hchar rfl hmlt
  · exact fun hg => hT.2.2 (hok.symm.trans h0) (hg.mono (by omega))

theorem markCore_spec (x : List ℕ) :
    Spec (bnd x)
      (fun σ => Frame x σ ∧ Tally x (σ.vars "i") σ ∧ σ.vars "i" < 3 * clauseCount x ∧
        σ.vars "u" = vAt x (σ.vars "i") ∧ σ.vars "e" = kAt x (σ.vars "i"))
      markCore
      (fun σ σ' => Frame x σ' ∧ Tally x (σ.vars "i" + 1) σ' ∧ σ'.vars "i" = σ.vars "i") 30 := by
  refine Spec.pre (P := fun σ => Frame x σ ∧ Tally x (σ.vars "i") σ ∧
      σ.vars "i" < 3 * clauseCount x ∧
      σ.vars "u" = vAt x (σ.vars "i") ∧ σ.vars "e" = kAt x (σ.vars "i") ∧
      σ.vars "V" = varCount x ∧ varCount x ≤ 3 * clauseCount x ∧
      x.length = 2 + 9 * clauseCount x ∧
      (σ.arrs "seen").length = 12 * x.length + 12 ∧
      σ.vars "u" < bnd x ∧ σ.vars "e" < bnd x ∧ σ.vars "V" < bnd x ∧
      4 * σ.vars "u" + 3 < bnd x ∧ (1 : ℕ) < bnd x ∧
      (σ.arrs "seen").getD (4 * σ.vars "u" + σ.vars "e") 0 < bnd x) ?_ ?_
  · run_vcg
    all_goals have hF : Frame x σ := ‹Frame x σ›
    all_goals have hT : Tally x (σ.vars "i") σ := ‹Tally x (σ.vars "i") σ›
    all_goals have hu : σ.vars "u" = vAt x (σ.vars "i") := ‹σ.vars "u" = vAt x (σ.vars "i")›
    all_goals have he : σ.vars "e" = kAt x (σ.vars "i") := ‹σ.vars "e" = kAt x (σ.vars "i")›
    all_goals have hV : σ.vars "V" = varCount x := ‹σ.vars "V" = varCount x›
    all_goals have hlen : x.length = 2 + 9 * clauseCount x := hF.2.2.2.1
    all_goals have hvle : varCount x ≤ 3 * clauseCount x := hF.2.2.2.2.1
    all_goals have hslen : (σ.arrs "seen").length = 12 * x.length + 12 := hF.2.2.2.2.2.2.1
    all_goals have hM : 4 * σ.vars "u" + σ.vars "e" = key x (σ.vars "i") := by rw [hu, he]; rfl
    · -- the bucket of this occurrence is already taken
      rename_i huv hev hzv
      simp only [Env.setVar] at hzv
      simp only [if_pos, if_neg] at hzv
      have hMlt : key x (σ.vars "i") < (σ.arrs "seen").length := by rw [← hM]; omega
      have hz : (σ.arrs "seen").getD (key x (σ.vars "i")) 0 = 1 := by
        rw [← hM]; simpa using hzv
      refine ⟨frame_congr x hF (by simp [Env.setVar]) (by simp [Env.setVar])
        (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar])
        (by simp [Env.setVar]), tally_fail x (by simp [Env.setVar]) ?_,
        by simp [Env.setVar]⟩
      rcases hT.1 with h0 | h1
      · exact fun hg => hT.2.2 h0 (hg.mono (by omega))
      · obtain ⟨hgood, hchar⟩ := hT.2.1 h1
        obtain ⟨i', hi', hkey⟩ := (hchar _ hMlt).mp hz
        exact not_good_succ_dup x (σ.vars "i") i' hi' (hgood.1 i' hi').2 (by rw [← he]; omega) hkey
    · -- the bucket is free, so claim it
      rename_i huv hev hzv
      simp only [Env.setVar] at hzv
      simp only [if_pos, if_neg] at hzv
      have hMlt : key x (σ.vars "i") < (σ.arrs "seen").length := by rw [← hM]; omega
      have hz : (σ.arrs "seen").getD (key x (σ.vars "i")) 0 ≠ 1 := by
        rw [← hM]; simpa using hzv
      refine ⟨frame_mark x hF hMlt (by simp [Env.setVar, Env.setArr])
        (by simp [Env.setVar, Env.setArr]) (by simp [Env.setVar, Env.setArr])
        (by simp [Env.setVar, Env.setArr]) (by rw [← hM]; simp [Env.setVar, Env.setArr])
        (by simp [Env.setVar, Env.setArr]),
        tally_mark x hT (by simp [Env.setVar, Env.setArr])
          (by rw [← hM]; simp [Env.setVar, Env.setArr]) hMlt hz ?_ ?_,
        by simp [Env.setVar, Env.setArr]⟩
      · rw [← hu, ← hV]; exact huv
      · rw [← he]; exact hev
    · -- the appearance index is out of range
      rename_i huv hev
      refine ⟨frame_congr x hF (by simp [Env.setVar]) (by simp [Env.setVar])
        (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar])
        (by simp [Env.setVar]), tally_fail x (by simp [Env.setVar]) ?_,
        by simp [Env.setVar]⟩
      exact not_good_succ x (σ.vars "i") (fun hc => hev (by rw [← he] at hc; exact hc.2))
    · -- the variable is out of range
      rename_i huv
      refine ⟨frame_congr x hF (by simp [Env.setVar]) (by simp [Env.setVar])
        (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar])
        (by simp [Env.setVar]), tally_fail x (by simp [Env.setVar]) ?_,
        by simp [Env.setVar]⟩
      exact not_good_succ x (σ.vars "i") (fun hc => huv (by rw [hu, hV]; exact hc.1))
    all_goals first
      | (have := length_lt_bnd x; omega)
      | simpa [Env.setVar] using ‹(σ.arrs "seen").getD (4 * σ.vars "u" + σ.vars "e") 0 < bnd x›
  · rintro σ ⟨hF, hT, hi, hu, he⟩
    obtain ⟨hV, hC, hT3, hlen, hvle, harr, hslen, hsone, hout⟩ := hF
    have hub : σ.vars "u" < bnd x := by
      rw [hu, vAt]; exact getD_lt_bnd x _
    have heb : σ.vars "e" < bnd x := by
      rw [he, kAt]; exact getD_lt_bnd x _
    refine ⟨⟨hV, hC, hT3, hlen, hvle, harr, hslen, hsone, hout⟩, hT, hi, hu, he, hV, hvle,
      hlen, hslen, hub, heb, by rw [hV]; exact varCount_lt_bnd x, ?_, ?_, ?_⟩
    · rw [hu, vAt]; exact four_getD_lt_bnd x _
    · have := length_lt_bnd x; omega
    · have h1 := hsone (4 * σ.vars "u" + σ.vars "e")
      have := length_lt_bnd x; omega

lemma forty_le_bnd (x : List ℕ) : 40 ≤ bnd x := by simp only [bnd]; omega

lemma three_clauseCount_lt_bnd (x : List ℕ) : 3 * clauseCount x < bnd x := by
  have := nine_clauseCount_lt_bnd x; omega

lemma aD_read_v (x : List ℕ) (i : ℕ) : (x.drop 2).getD (3 * i) 0 = vAt x i := by
  rw [drop2_getD]; rfl

lemma aD_read_k (x : List ℕ) (i : ℕ) : (x.drop 2).getD (3 * i + 2) 0 = kAt x i := by
  rw [drop2_getD, kAt, show 2 + (3 * i + 2) = 2 + 3 * i + 2 from by omega]

lemma tally_congr (x : List ℕ) {n : ℕ} {σ σ' : Env} (h : Tally x n σ)
    (hok : σ'.vars "ok" = σ.vars "ok") (hs : σ'.arrs "seen" = σ.arrs "seen") :
    Tally x n σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hok]; exact h1, fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨hg, hc⟩ := h2 (hok.symm.trans hh)
    exact ⟨hg, by rw [hs]; exact hc⟩
  · exact h3 (hok.symm.trans hh)

/-- The core again, with the counter named, in the form a step of the loop composes
with. -/
theorem markCore_spec' (x : List ℕ) (n : ℕ) :
    Spec (bnd x)
      (fun σ => Frame x σ ∧ Tally x n σ ∧ σ.vars "i" = n ∧ n < 3 * clauseCount x ∧
        σ.vars "u" = vAt x n ∧ σ.vars "e" = kAt x n)
      markCore
      (fun _ σ' => Frame x σ' ∧ Tally x (n + 1) σ' ∧ σ'.vars "i" = n) 30 := by
  intro σ hσ
  obtain ⟨hF, hT, hin, hlt, hu, he⟩ := hσ
  subst hin
  obtain ⟨σ', hr, h1, h2, h3⟩ := markCore_spec x σ ⟨hF, hT, hlt, hu, he⟩
  exact ⟨σ', hr, h1, h2, h3⟩

lemma setVar_self (τ : Env) (y : String) (v : ℕ) : (τ.setVar y v).vars y = v := by
  simp [Env.setVar]

theorem markBody_aux (x : List ℕ) (n : ℕ) :
    Spec (bnd x) (fun σ => MInv x σ ∧ σ.vars "i" = n ∧ n < 3 * clauseCount x) markBody
      (fun _ σ' => MInv x σ' ∧ σ'.vars "i" = n + 1) 50 := by
  refine Spec.pre (P := fun σ => MInv x σ ∧ σ.vars "i" = n ∧ n < 3 * clauseCount x ∧
      40 ≤ bnd x ∧ 3 * n + 2 < bnd x ∧ n + 1 < bnd x ∧
      (σ.arrs "a").length = 9 * clauseCount x ∧
      (σ.arrs "a").getD (3 * n) 0 < bnd x ∧
      (σ.arrs "a").getD (3 * n + 2) 0 < bnd x ∧
      σ.arrs "a" = x.drop 2) ?_ ?_
  · run_vcg [markCore_spec' x n]
    all_goals have hI : MInv x σ := ‹MInv x σ›
    all_goals have hin : σ.vars "i" = n := ‹σ.vars "i" = n›
    all_goals have hn : n < 3 * clauseCount x := ‹n < 3 * clauseCount x›
    all_goals have harr : σ.arrs "a" = x.drop 2 := ‹σ.arrs "a" = x.drop 2›
    all_goals try (have h40 := forty_le_bnd x; omega)
    all_goals try (simpa [Env.setVar, hin] using ‹(σ.arrs "a").getD (3 * n) 0 < bnd x›)
    all_goals try (simpa [Env.setVar, hin] using ‹(σ.arrs "a").getD (3 * n + 2) 0 < bnd x›)
    all_goals first
      | -- the precondition of the core
        (refine And.intro (frame_congr x hI.1 (by simp [Env.setVar]) (by simp [Env.setVar])
            (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar])
            (by simp [Env.setVar]))
          (And.intro (tally_congr x (hin ▸ hI.2.2) (by simp [Env.setVar])
              (by simp [Env.setVar]))
          (And.intro (by simp [Env.setVar, hin]) (And.intro hn (And.intro ?_ ?_))))
         · have hread : (σ.arrs "a").getD (3 * σ.vars "i") 0 = vAt x n := by
             rw [harr, hin, aD_read_v]
           simpa [Env.setVar] using hread
         · have hread : (σ.arrs "a").getD (3 * σ.vars "i" + 2) 0 = kAt x n := by
             rw [harr, hin, aD_read_k]
           simpa [Env.setVar] using hread)
      | -- what the body computed
        (obtain ⟨hFr, hTa, hieq⟩ := ‹Frame x _ ∧ Tally x (n + 1) _ ∧ _›
         refine And.intro (And.intro (frame_congr x hFr (by simp [Env.setVar])
             (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar])
             (by simp [Env.setVar]) (by simp [Env.setVar])) (And.intro ?_ ?_)) ?_
         · rw [setVar_self, hieq]; omega
         · rw [setVar_self, hieq]
           exact tally_congr x hTa (by simp [Env.setVar]) (by simp [Env.setVar])
         · rw [setVar_self, hieq])
  · rintro σ ⟨hI, hin, hn⟩
    have harr : σ.arrs "a" = x.drop 2 := hI.1.2.2.2.2.2.1
    have halen : (σ.arrs "a").length = 9 * clauseCount x := a_len x hI.1
    have h40 := forty_le_bnd x
    have h3c := three_clauseCount_lt_bnd x
    have h9c := nine_clauseCount_lt_bnd x
    refine ⟨hI, hin, hn, h40, by omega, by omega, halen, ?_, ?_, harr⟩
    · rw [harr, aD_read_v, vAt]; exact getD_lt_bnd x _
    · rw [harr, aD_read_k, kAt]; exact getD_lt_bnd x _

theorem markBody_spec (x : List ℕ) :
    Spec (bnd x) (fun σ => MInv x σ ∧ σ.vars "i" < 3 * clauseCount x) markBody
      (fun σ σ' => MInv x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 50 := by
  intro σ hσ
  obtain ⟨σ', hr, hq1, hq2⟩ := markBody_aux x (σ.vars "i") σ ⟨hσ.1, rfl, hσ.2⟩
  exact ⟨σ', hr, hq1, hq2⟩

/-- **The marking pass.** -/
theorem markLoop_spec (x : List ℕ) :
    Spec (bnd x) (fun σ => MInv x (σ.setVar "i" 0)) markLoop
      (fun _ σ' => MInv x σ' ∧ σ'.vars "i" = 3 * clauseCount x)
      ((50 + 4) * (3 * clauseCount x) + 6) :=
  Spec.forRangeZero "i" "T3" (MInv x) (3 * clauseCount x) 50
    (three_clauseCount_lt_bnd x)
    (fun _ h => h.2.1) (fun _ h => h.1.2.2.1) (markBody_spec x)

/-- What splitting off the header leaves behind. -/
def Pre2 (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "V" = varCount x ∧ σ.vars "C" = clauseCount x ∧ σ.vars "len" = x.length ∧
    σ.arrs "a" = x.drop 2 ∧ σ.arrs "seen" = List.replicate (12 * x.length + 12) 0 ∧
    σ.out = []

theorem wLoop_spec' (x : List ℕ) :
    Spec (bnd x) (fun σ => WInv x (σ.setVar "t" 0)) wLoop
      (fun _ σ' => (∀ i, (σ'.arrs "w").getD i 0 = x.getD i 0) ∧
        (σ'.arrs "w").getD 0 0 = varCount x ∧ (σ'.arrs "w").getD 1 0 = clauseCount x ∧
        (σ'.arrs "w").length = x.length + 2 ∧ σ'.vars "len" = x.length ∧
        (σ'.arrs "a").length = x.length - 2 ∧
        σ'.arrs "seen" = List.replicate (12 * x.length + 12) 0 ∧
        σ'.out = []) (12 * x.length + 6) := by
  intro σ hσ
  obtain ⟨σ', hr, hI, ht⟩ := wLoop_spec x σ hσ
  have hall := w_read x hI ht
  exact ⟨σ', hr, hall, hall 0, hall 1, hI.2.2.1, hI.1, hI.2.2.2.2.2.1,
    hI.2.2.2.2.2.2.1, hI.2.2.2.2.2.2.2.2⟩

theorem aLoop_spec' (x : List ℕ) :
    Spec (bnd x) (fun σ => AInv x (σ.setVar "q" 0)) aLoop
      (fun _ σ' => Pre2 x σ') (14 * (x.length - 2) + 6) := by
  intro σ hσ
  obtain ⟨σ', hr, hI, hq⟩ := aLoop_spec x σ hσ
  exact ⟨σ', hr, hI.2.1, hI.2.2.1, hI.1, arr_a_eq x hI hq,
    hI.2.2.2.2.2.2.2.2.2.1, hI.2.2.2.2.2.2.2.2.2.2⟩

/-- The environment the program starts in. -/
def Init (x : List ℕ) (σ : Env) : Prop :=
  σ.inp = x.length :: x ∧ σ.out = [] ∧
    (σ.arrs "w").length = x.length + 2 ∧ (∀ i, (σ.arrs "w").getD i 0 = 0) ∧
    (σ.arrs "a").length = x.length - 2 ∧
    σ.arrs "seen" = List.replicate (12 * x.length + 12) 0

/-- What the three immediate checks leave behind. -/
def Mid (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "V" = varCount x ∧ σ.vars "C" = clauseCount x ∧
    σ.vars "T3" = 3 * clauseCount x ∧ σ.arrs "a" = x.drop 2 ∧
    σ.arrs "seen" = List.replicate (12 * x.length + 12) 0 ∧ σ.out = [] ∧
    (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1) ∧
    (σ.vars "ok" = 1 ↔ (x.length = 2 + 9 * clauseCount x ∧ varCount x ≤ 3 * clauseCount x))

lemma wInv_of_init (x : List ℕ) {σ : Env} (h : Init x σ) :
    WInv x (({ σ.setVar "len" (σ.inp.headD 0) with inp := σ.inp.tail } : Env).setVar "t" 0) := by
  obtain ⟨hinp, hout, hwlen, hwz, halen, hseen⟩ := h
  simp only [WInv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (simp [Env.setVar, hinp, hout, hwlen, halen, hseen]; done)
      | (intro i hi; exact hwz i)

theorem checkRead_spec (x : List ℕ) :
    Spec (bnd x) (Init x) checkRead (fun _ σ' => Pre2 x σ') (26 * x.length + 30) := by
  refine Spec.pre (P := fun σ => Init x σ ∧ 40 ≤ bnd x ∧ x.length + 1 < bnd x ∧
      2 + 9 * clauseCount x < bnd x ∧ varCount x < bnd x ∧ clauseCount x < bnd x ∧
      3 * clauseCount x < bnd x) ?_ ?_
  · run_vcg [wLoop_spec' x, aLoop_spec' x]
    all_goals have hI : Init x σ := ‹Init x σ›
    all_goals first
      | assumption
      | (rw [hI.1]; simp; done)
      | (exact wInv_of_init x hI)
      | omega
      | (simp only [Env.setVar]; omega)
      | (obtain ⟨hw1, hw0, hwc, hwl, hwlen', hal, hs, ho⟩ :=
           ‹(∀ (i : ℕ), _) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _›
         simp only [AInv]
         refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
         · simpa [Env.setVar] using hwlen'
         · simpa [Env.setVar] using hw0
         · simpa [Env.setVar] using hwc
         · simp [Env.setVar, hwlen']
         · simp [Env.setVar]
         · simpa [Env.setVar] using hwl
         · intro i; exact hw1 i
         · simpa [Env.setVar] using hal
         · simp [Env.setVar]
         · simpa [Env.setVar] using hs
         · simpa [Env.setVar] using ho)
  · intro σ h
    exact ⟨h, forty_le_bnd x, length_lt_bnd x, nine_clauseCount_lt_bnd x,
      varCount_lt_bnd x, clauseCount_lt_bnd x, three_clauseCount_lt_bnd x⟩

theorem checkTests_spec (x : List ℕ) :
    Spec (bnd x) (Pre2 x) checkTests (fun _ σ' => Mid x σ') 30 := by
  refine Spec.pre (P := fun σ => Pre2 x σ ∧ 40 ≤ bnd x ∧ x.length + 1 < bnd x ∧
      2 + 9 * clauseCount x < bnd x ∧ varCount x < bnd x ∧ clauseCount x < bnd x ∧
      3 * clauseCount x < bnd x ∧ σ.vars "V" = varCount x ∧ σ.vars "C" = clauseCount x ∧
      σ.vars "len" = x.length) ?_ ?_
  · run_vcg
    all_goals try omega
    all_goals try (simp only [Env.setVar]; omega)
    all_goals obtain ⟨hV, hC, hlen, ha, hs, ho⟩ := ‹Pre2 x σ›
    all_goals simp only [Mid]
    all_goals refine ⟨by simp [Env.setVar, hV], by simp [Env.setVar, hC],
      by simp [Env.setVar, hC], by simpa [Env.setVar] using ha,
      by simpa [Env.setVar] using hs, by simpa [Env.setVar] using ho,
      by simp [Env.setVar], ?_⟩
    all_goals simp only [Env.setVar]
    all_goals try simp_all
    all_goals omega
  · intro σ h
    exact ⟨h, forty_le_bnd x, length_lt_bnd x, nine_clauseCount_lt_bnd x, varCount_lt_bnd x,
      clauseCount_lt_bnd x, three_clauseCount_lt_bnd x, h.1, h.2.1, h.2.2.1⟩

theorem checkHead_spec (x : List ℕ) :
    Spec (bnd x) (Init x) checkHead (fun _ σ' => Mid x σ') (26 * x.length + 60) := by
  run_vcg [checkRead_spec x, checkTests_spec x]
  all_goals first
    | assumption
    | omega

/-! ### The Decision, Assembled -/

/-- What the whole decision leaves behind. -/
def Final (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "V" = varCount x ∧ σ.vars "C" = clauseCount x ∧ σ.arrs "a" = x.drop 2 ∧
    σ.out = [] ∧ (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1) ∧
    (σ.vars "ok" = 1 ↔ WellFormed x)

lemma replicate_getD (n m : ℕ) : (List.replicate n 0).getD m 0 = 0 := by
  rcases Nat.lt_or_ge m n with hm | hm
  · rw [List.getD_eq_getElem _ _ (by simpa using hm)]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hm), Option.getD_none]

lemma mInv_start (x : List ℕ) {σ : Env} (h : Mid x σ) (hok : σ.vars "ok" = 1) :
    MInv x (σ.setVar "i" 0) := by
  obtain ⟨hV, hC, hT3, ha, hs, ho, h01, hiff⟩ := h
  obtain ⟨hlen, hvle⟩ := hiff.mp hok
  have hrfl : (σ.setVar "i" 0).arrs "seen" = σ.arrs "seen" := rfl
  have hz : ∀ m, (σ.arrs "seen").getD m 0 = 0 := by
    intro m; rw [hs]; exact replicate_getD _ m
  have hival : (σ.setVar "i" 0).vars "i" = 0 := by simp [Env.setVar]
  refine ⟨⟨by simpa [Env.setVar] using hV, by simpa [Env.setVar] using hC,
      by simpa [Env.setVar] using hT3, hlen, hvle, by simpa [Env.setVar] using ha,
      ?_, ?_, by simpa [Env.setVar] using ho⟩, by simp [Env.setVar], ?_⟩
  · rw [hrfl, hs]; simp
  · intro m; rw [hrfl, hz m]; omega
  · rw [hival]
    refine ⟨Or.inr (by simpa [Env.setVar] using hok), fun _ => ⟨?_, ?_⟩, ?_⟩
    · exact ⟨fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩
    · intro m _
      constructor
      · intro h1
        exfalso
        rw [hrfl, hz m] at h1
        omega
      · rintro ⟨i', hi', -⟩
        exact absurd hi' (by omega)
    · intro h0
      exact absurd (h0.symm.trans (by simpa [Env.setVar] using hok)) (by omega)

lemma final_of_mark (x : List ℕ) {σ σ' : Env} (hM : Mid x σ) (hok : σ.vars "ok" = 1)
    (h : MInv x σ' ∧ σ'.vars "i" = 3 * clauseCount x) : Final x σ' := by
  obtain ⟨⟨hF, -, hT⟩, hi⟩ := h
  obtain ⟨hlen, hvle⟩ := hM.2.2.2.2.2.2.2.mp hok
  refine ⟨hF.1, hF.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.2, hT.1, ?_⟩
  rw [wellFormed_iff]
  constructor
  · intro h1
    exact ⟨hlen, hvle, by rw [← hi]; exact (hT.2.1 h1).1⟩
  · intro h1
    rcases hT.1 with h0 | h1'
    · exact absurd (show Good x (σ'.vars "i") by rw [hi]; exact h1.2.2) (hT.2.2 h0)
    · exact h1'

lemma final_of_skip (x : List ℕ) {σ : Env} (hM : Mid x σ) (hok : ¬ σ.vars "ok" = 1) :
    Final x σ := by
  obtain ⟨hV, hC, hT3, ha, hs, ho, h01, hiff⟩ := hM
  refine ⟨hV, hC, ha, ho, h01, ?_⟩
  constructor
  · intro h; exact absurd h hok
  · intro h
    obtain ⟨h1, h2, -⟩ := (wellFormed_iff x).mp h
    exact hiff.mpr ⟨h1, h2⟩

theorem checkBody_spec (x : List ℕ) :
    Spec (bnd x) (Mid x) checkBody (fun _ σ' => Final x σ')
      ((50 + 4) * (3 * clauseCount x) + 10) := by
  refine Spec.pre (P := fun σ => Mid x σ ∧ 40 ≤ bnd x ∧ σ.vars "ok" ≤ 1) ?_ ?_
  · run_vcg [markLoop_spec x]
    all_goals have hM : Mid x σ := ‹Mid x σ›
    all_goals first
      | omega
      | (exact mInv_start x hM ‹σ.vars "ok" = 1›)
      | (apply final_of_mark x hM ‹σ.vars "ok" = 1›; assumption)
      | (exact final_of_skip x hM ‹¬ σ.vars "ok" = 1›)
  · intro σ h
    exact ⟨h, forty_le_bnd x, by rcases h.2.2.2.2.2.2.1 with h0 | h1 <;> omega⟩

/-! ### Costing the whole program

A word whose header lies about its length is rejected by the first check, and the
marking pass and the emitter are then both skipped. So the loop bounds a cost has to be
stated in — the number of clauses, the number of jobs — are bounded by the length of the
word on every path that reaches them, and the whole program is linear in that length.
That is why each phase is costed twice, once on each side of the check it is guarded
by. -/

/-- The two conditions the immediate checks decide. -/
def Header (x : List ℕ) : Prop :=
  x.length = 2 + 9 * clauseCount x ∧ varCount x ≤ 3 * clauseCount x

lemma markLoop_vacuous (x : List ℕ) (h : ¬ Header x) (K : ℕ) :
    Spec (bnd x) (fun σ => MInv x (σ.setVar "i" 0) ∧ σ.vars "ok" = 1) markLoop
      (fun _ σ' => MInv x σ' ∧ σ'.vars "i" = 3 * clauseCount x) K := by
  intro σ hσ
  exact absurd ⟨hσ.1.1.2.2.2.1, hσ.1.1.2.2.2.2.1⟩ h

theorem checkBody_spec_small (x : List ℕ) (h : ¬ Header x) :
    Spec (bnd x) (Mid x) checkBody (fun _ σ' => Final x σ') 5 := by
  refine Spec.pre (P := fun σ => Mid x σ ∧ 40 ≤ bnd x ∧ σ.vars "ok" ≤ 1) ?_ ?_
  · run_vcg [markLoop_vacuous x h 1]
    all_goals have hM : Mid x σ := ‹Mid x σ›
    all_goals first
      | omega
      | (exact And.intro (mInv_start x hM ‹σ.vars "ok" = 1›) ‹σ.vars "ok" = 1›)
      | (apply final_of_mark x hM ‹σ.vars "ok" = 1›; assumption)
      | (exact final_of_skip x hM ‹¬ σ.vars "ok" = 1›)
  · intro σ h'
    exact ⟨h', forty_le_bnd x, by rcases h'.2.2.2.2.2.2.1 with h0 | h1 <;> omega⟩

/-- **The decision, at a cost linear in the length of the word.** -/
theorem checkBody_spec_lin (x : List ℕ) :
    Spec (bnd x) (Mid x) checkBody (fun _ σ' => Final x σ') (162 * x.length + 10) := by
  by_cases h : Header x
  · exact (checkBody_spec x).mono (by have := h.1; omega)
  · exact (checkBody_spec_small x h).mono (by omega)

theorem checker_spec_lin (x : List ℕ) :
    Spec (bnd x) (Init x) checker (fun _ σ' => Final x σ') (188 * x.length + 70) := by
  run_vcg [checkHead_spec x, checkBody_spec_lin x]
  all_goals first
    | assumption
    | omega

/-! ### The Two Branches -/

theorem noPart_spec (x : List ℕ) :
    Spec (bnd x) (fun σ => σ.out = []) noPart (fun _ σ' => σ'.out = noWord) 21 := by
  refine Spec.pre (P := fun σ => σ.out = [] ∧ 40 ≤ bnd x) ?_ ?_
  · run_vcg
    all_goals first
      | omega
      | (simp [noWord, ‹σ.out = []›])
  · exact fun σ h => ⟨h, forty_le_bnd x⟩

theorem emitPart_spec (x : List ℕ) (hwf : WellFormed x) :
    Spec (bnd x)
      (fun σ => σ.vars "V" = nVar x ∧ σ.vars "C" = nCla x ∧
        σ.arrs "a" = x.drop 2 ∧ σ.out = [])
      emitPart (fun _ σ' => σ'.out = emit x) (108 * nCla x + 366 * nJobs x + 88) := by
  refine Spec.pre (P := fun σ => σ.vars "V" = nVar x ∧ σ.vars "C" = nCla x ∧
      σ.arrs "a" = x.drop 2 ∧ σ.out = [] ∧
      40 * nCla x + 40 * nVar x + 64 < bnd x) ?_ ?_
  · run_vcg [procLoop_spec x hwf (pre0 x), dueLoop_spec x hwf (pre1 x),
      wtLoop_spec x hwf (pre2 x), offLoop_spec x hwf (pre3 x), tgtLoop_spec x hwf (pre4 x)]
    all_goals have hV : σ.vars "V" = nVar x := ‹σ.vars "V" = nVar x›
    all_goals have hC : σ.vars "C" = nCla x := ‹σ.vars "C" = nCla x›
    all_goals have ha : σ.arrs "a" = x.drop 2 := ‹σ.arrs "a" = x.drop 2›
    all_goals have ho : σ.out = [] := ‹σ.out = []›
    all_goals have hsm : 40 * nCla x + 40 * nVar x + 64 < bnd x := small_lt_bnd x hwf
    all_goals have hnj : nJobs x = nVar x + 9 * nCla x := rfl
    all_goals have hnm : nMach x = 2 * nVar x + 3 * nCla x := rfl
    all_goals try simp only [Ctx, BInv, BInvL] at *
    all_goals try simp_all [pre0, pre1, pre2, pre3, pre4, procBlock, dueBlock, wtBlock,
      offBlock, tgtBlock]
    all_goals try and_intros
    all_goals first
      | rfl
      | assumption
      | omega
      | simp
      | (simp; omega)
      | (simp [emit, procBlock, dueBlock, wtBlock, offBlock, tgtBlock, nJobs, nMach])
  · rintro σ ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4, small_lt_bnd x hwf⟩

/-! ### The Two Branches, Chosen -/

lemma emitPartR_spec (x : List ℕ) (hwf : WellFormed x) :
    Spec (bnd x) (Final x) emitPart (fun _ σ' => σ'.out = reduce x)
      (108 * nCla x + 366 * nJobs x + 88) := by
  have hr : reduce x = emit x := by simp [reduce, hwf]
  intro σ hσ
  obtain ⟨σ', hrun, hout⟩ := emitPart_spec x hwf σ ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1⟩
  exact ⟨σ', hrun, by rw [hr]; exact hout⟩

lemma noPartR_spec (x : List ℕ) (hwf : ¬ WellFormed x) :
    Spec (bnd x) (Final x) noPart (fun _ σ' => σ'.out = reduce x) 21 := by
  have hr : reduce x = noWord := by simp [reduce, hwf]
  intro σ hσ
  obtain ⟨σ', hrun, hout⟩ := noPart_spec x σ hσ.2.2.2.1
  exact ⟨σ', hrun, by rw [hr]; exact hout⟩

lemma emitPart_vacuous (x : List ℕ) (hwf : ¬ WellFormed x) (K : ℕ) :
    Spec (bnd x) (fun σ => Final x σ ∧ σ.vars "ok" = 1) emitPart
      (fun _ σ' => σ'.out = reduce x) K :=
  fun _ hσ => absurd (hσ.1.2.2.2.2.2.mp hσ.2) hwf

lemma noPart_vacuous (x : List ℕ) (hwf : WellFormed x) (K : ℕ) :
    Spec (bnd x) (fun σ => Final x σ ∧ ¬ σ.vars "ok" = 1) noPart
      (fun _ σ' => σ'.out = reduce x) K :=
  fun _ hσ => absurd (hσ.1.2.2.2.2.2.mpr hwf) hσ.2

theorem tail_spec (x : List ℕ) :
    Spec (bnd x) (Final x) tailCom (fun _ σ' => σ'.out = reduce x) (4500 * x.length + 92) := by
  by_cases hwf : WellFormed x
  · have hlen := hwf.length_eq
    have hvle := hwf.var_le
    have hnj : nJobs x = varCount x + 9 * clauseCount x := rfl
    have hnc : nCla x = clauseCount x := rfl
    have hnv : nVar x = varCount x := rfl
    refine Spec.mono (K := 108 * nCla x + 366 * nJobs x + 92) ?_ (by omega)
    refine Spec.pre (P := fun σ => Final x σ ∧ 40 ≤ bnd x ∧ σ.vars "ok" ≤ 1) ?_ ?_
    · run_vcg [emitPartR_spec x hwf, noPart_vacuous x hwf (108 * nCla x + 366 * nJobs x + 88)]
      all_goals first
        | omega
        | assumption
        | (refine And.intro ?_ ?_ <;> assumption)
    · intro σ h
      exact ⟨h, forty_le_bnd x, by rcases h.2.2.2.2.1 with h0 | h1 <;> omega⟩
  · refine Spec.mono (K := 25) ?_ (by omega)
    refine Spec.pre (P := fun σ => Final x σ ∧ 40 ≤ bnd x ∧ σ.vars "ok" ≤ 1) ?_ ?_
    · run_vcg [emitPart_vacuous x hwf 21, noPartR_spec x hwf]
      all_goals first
        | omega
        | assumption
        | (refine And.intro ?_ ?_ <;> assumption)
    · intro σ h
      exact ⟨h, forty_le_bnd x, by rcases h.2.2.2.2.1 with h0 | h1 <;> omega⟩

/-- **The program computes the reduction.** -/
theorem com_spec (x : List ℕ) :
    Spec (bnd x) (Init x) com (fun _ σ' => σ'.out = reduce x) (4688 * x.length + 162) := by
  run_vcg [checker_spec_lin x, tail_spec x]
  all_goals first
    | assumption
    | omega

/-! ### From IMP+ to the Machine -/

/-- The physical inputs the program is written for: a word preceded by its length. -/
def Shape : Set (List ℕ) := {y | y ≠ [] ∧ y.headD 0 = y.tail.length}

lemma shape_eq {y : List ℕ} (h : y ∈ Shape) : y = y.tail.length :: y.tail := by
  obtain ⟨hne, hh⟩ := h
  rcases y with _ | ⟨a, t⟩
  · exact absurd rfl hne
  · simp only [List.headD_cons, List.tail_cons] at hh ⊢
    rw [hh]

/-- The array lengths the program needs. -/
def extOf (x : List ℕ) : String → ℕ := fun a =>
  if a = "w" then x.length + 2 else
  if a = "a" then x.length - 2 else
  if a = "seen" then 12 * x.length + 12 else 0

/-- The reduction, as a function of the physical input. -/
noncomputable def red (y : List ℕ) : List ℕ := reduce y.tail

theorem solves : Solves layout com Shape red (fun y => bnd y.tail)
    (fun y => 4688 * y.tail.length + 162) where
  ok := com_ok
  inp := by
    intro y hy v hv
    rw [shape_eq hy] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · have := length_lt_bnd y.tail; omega
    · exact entry_lt_bnd y.tail hv'
  run := by
    intro y hy
    have hpre : Init y.tail (initEnv (extOf y.tail) y) := by
      refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
      · show y = _
        exact shape_eq hy
      · simp [initEnv, extOf]
      · intro i
        show (List.replicate (extOf y.tail "w") 0).getD i 0 = 0
        exact replicate_getD _ i
      · simp [initEnv, extOf]
      · simp [initEnv, extOf]
    obtain ⟨σ', hrun, hout⟩ := com_spec y.tail (initEnv (extOf y.tail) y) hpre
    exact ⟨extOf y.tail, σ', hrun, hout⟩

/-- The machine program. -/
def prog : Program := compileProgram layout com

theorem prog_computesInTime (w : ℕ) :
    ComputesInTime w prog
      {y | y ∈ Shape ∧ Lax470956.ParameterizedComplexity.Fits 46880 w y}
      red (fun y => 46880 * (y.length + 1)) := by
  have hs : Solves layout com
      {y | y ∈ Shape ∧ Lax470956.ParameterizedComplexity.Fits 46880 w y} red
      (fun y => bnd y.tail) (fun y => 4688 * y.tail.length + 162) :=
    ⟨solves.ok, fun y hy => solves.inp y hy.1, fun y hy => solves.run y hy.1⟩
  refine computesInTime_of_solves hs (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨hsh, hfits⟩ := hy
    have hne : y.headD 0 ∈ y := by
      rcases y with _ | ⟨a, t⟩
      · exact absurd rfl hsh.1
      · simpa using List.mem_cons_self
    have hylen : y.length = y.tail.length + 1 := by
      rcases y with _ | ⟨a, t⟩
      · exact absurd rfl hsh.1
      · simp
    have hbig : 46880 * (y.length + y.tail.foldr max 0 + 1) ≤ 2 ^ w := by
      rcases Lax470956Proofs.Pmax.foldr_max_mem_or_zero y.tail with hm | hm
      · exact hfits _ (by rw [shape_eq hsh]; exact List.mem_cons_of_mem _ hm)
      · rw [hm]
        have := hfits _ hne
        omega
    refine fitsWords_of_max_le (by simp only [bnd]; omega) ?_
    simp only [Layout.span, layout, List.length_cons, List.length_nil, bnd, max_le_iff]
    omega
  · have hylen : y.length = y.tail.length + 1 := by
      rcases y with _ | ⟨a, t⟩
      · exact absurd rfl hy.1.1
      · simp
    rw [const_eq]
    omega

/-! ### The entries of the emitted word

`RamPolytime` asks that the output be words too, so the entries of the emitted word have
to be bounded — by the same bound the run itself stays under, which is all any of them
is. -/

lemma dueOf_le_25 (x : List ℕ) (j : ℕ) : dueOf x j ≤ 25 := by
  by_cases h : j < nVar x
  · simp [dueOf_lt x h]
  · rw [dueOf_ge x h]
    have h2 := dl_le x (cOf (j - nVar x)) (hOf (j - nVar x))
    split_ifs <;> omega

lemma procBlock_lt (x : List ℕ) {v : ℕ} (hv : v ∈ procBlock x) : v < bnd x := by
  simp only [procBlock, List.mem_map, List.mem_range] at hv
  obtain ⟨j, -, rfl⟩ := hv
  have h1 := procOf_le_25 x j
  have h2 := forty_le_bnd x
  omega

lemma dueBlock_lt (x : List ℕ) {v : ℕ} (hv : v ∈ dueBlock x) : v < bnd x := by
  simp only [dueBlock, List.mem_map, List.mem_range] at hv
  obtain ⟨j, -, rfl⟩ := hv
  have h1 := dueOf_le_25 x j
  have h2 := forty_le_bnd x
  omega

lemma wtBlock_lt (x : List ℕ) {v : ℕ} (hv : v ∈ wtBlock x) : v < bnd x := by
  simp only [wtBlock, List.mem_replicate] at hv
  have h2 := forty_le_bnd x
  omega

lemma offBlock_lt (x : List ℕ) (hwf : WellFormed x) {v : ℕ} (hv : v ∈ offBlock x) :
    v < bnd x := by
  simp only [offBlock, List.mem_map, List.mem_range] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  have h1 := off_lt_bnd x hwf (j := j) (by omega)
  have h2 := two_mul_lt_bnd x hwf (j := j) (by omega)
  simp only [offOf]
  split <;> omega

lemma tgtBlock_lt (x : List ℕ) (hwf : WellFormed x) {v : ℕ} (hv : v ∈ tgtBlock x) :
    v < bnd x := by
  simp only [tgtBlock, List.mem_flatMap, List.mem_range] at hv
  obtain ⟨j, hj, hmem⟩ := hv
  have hsm := small_lt_bnd x hwf
  have hnj : nJobs x = nVar x + 9 * nCla x := rfl
  have hvle := wf_var_le x hwf
  by_cases hlt : j < nVar x
  · rw [eligOf_lt x hlt] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> omega
  · have hc : cOf (j - nVar x) < nCla x := by simp only [cOf]; omega
    have hlv : 4 * litVar x (cOf (j - nVar x)) (hOf (j - nVar x)) + 3 < bnd x :=
      four_getD_lt_bnd x (2 + 9 * cOf (j - nVar x) + 3 * hOf (j - nVar x))
    rw [eligOf_ge x hlt] at hmem
    split at hmem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · omega
      · omega
      · split <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;> omega

lemma emit_lt_bnd (x : List ℕ) (hwf : WellFormed x) {v : ℕ} (hv : v ∈ emit x) : v < bnd x := by
  have hsm := small_lt_bnd x hwf
  have hjl := nJobs_le x hwf
  have hml := nMach_le x hwf
  simp only [emit, List.mem_append] at hv
  rcases hv with ((((h | h) | h) | h) | h) | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> omega
  · exact procBlock_lt x h
  · exact dueBlock_lt x h
  · exact wtBlock_lt x h
  · exact offBlock_lt x hwf h
  · exact tgtBlock_lt x hwf h

lemma reduce_lt_bnd (x : List ℕ) {v : ℕ} (hv : v ∈ reduce x) : v < bnd x := by
  have h40 := forty_le_bnd x
  by_cases hwf : WellFormed x
  · rw [show reduce x = emit x from by simp [reduce, hwf]] at hv
    exact emit_lt_bnd x hwf hv
  · rw [show reduce x = noWord from by simp [reduce, hwf]] at hv
    simp only [noWord, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-! ### Polynomial Time, in the Bit-Size Currency -/

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding

lemma bnd_le_pow (x : List ℕ) : bnd x ≤ 2 ^ (bitSize x + 8) := by
  have h1 : x.length ≤ bitSize x := length_le_bitSize x
  have h2 : x.foldr max 0 < 2 ^ (bitSize x + 1) := by
    rcases Lax470956Proofs.Pmax.foldr_max_mem_or_zero x with hm | hm
    · exact mem_lt_two_pow_bitSize_add_one hm
    · rw [hm]; positivity
  have h3 : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
  have h4 : (2:ℕ) ^ (bitSize x + 1) = 2 * 2 ^ bitSize x := by ring
  have h5 : (2:ℕ) ^ (bitSize x + 8) = 256 * 2 ^ bitSize x := by ring
  have h6 : 1 ≤ (2:ℕ) ^ bitSize x := Nat.one_le_two_pow
  simp only [bnd]
  omega

/-- **The reduction is computable in polynomial time by a word RAM.** -/
theorem ramPolytime_reduce : RamPolytime reduce := by
  refine Lax470956Proofs.RamBridge.ramPolytime_of (c := 46880) (K := 24) (prog := prog)
    (by omega) (by norm_num) ?_ ?_
  · intro x v hv
    have h1 := reduce_lt_bnd x hv
    have h2 := bnd_le_pow x
    have h3 : (2:ℕ) ^ (bitSize x + 8) ≤ 2 ^ (bitSize x + 24) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · intro w x hfits
    have hy : (x.length :: x) ∈ Shape := ⟨by simp, by simp⟩
    have hf : Lax470956.ParameterizedComplexity.Fits 46880 w (x.length :: x) := by
      intro v hv
      simpa using hfits v hv
    obtain ⟨t, ht, hrun⟩ := prog_computesInTime w (x.length :: x) ⟨hy, hf⟩
    exact ⟨t, by simpa using ht, by simpa [red] using hrun⟩

/--
---
conclusion: Lax470956.Construction2.reduce_ramPolytime
---
The program reads its input into an array, decides well-formedness in one pass over the
literal slots, and then either runs the emitter of `EmitProg` — whose five passes are
reused here through the specification each of them carries — or writes the seven-entry
word a malformed input is sent to.

Three of the four conditions are immediate. The fourth, that distinct occurrences of one
variable carry distinct appearance indices, is decided by bucketing: an occurrence of
variable `v` with appearance index `k` claims the cell `4v + k`, and a cell claimed twice
refutes the condition. The cells fit because the pass runs only when the other three
checks have passed, so `v < V ≤ 3C` and `k < 4`.

Each phase is costed twice, once on each side of the check that guards it. A word whose
header lies about its length is rejected by the first check, and the marking pass and the
emitter are then both skipped; that is what keeps the cost linear in the length of the
word rather than in the number the word claims is its clause count. The whole is
`4688 · |x| + 162` units of IMP+ cost, so `46880 · (|x| + 2)` machine instructions.

What remains is a change of currency, which `RamBridge` does once: the bit size bounds
the number of entries, and every value the program forms is bounded by the length of the
word plus its largest entry, hence by `2 ^ (bitSize x + 8)`.
-/
theorem reduce_ramPolytime : RamPolytime reduce := ramPolytime_reduce

open Lax470956.PolynomialReduction Lax470956.InstanceEncoding Lax470956.Scheduling in
/--
---
conclusion: Lax470956.Theorem2.sat34_polyReducesOn_allSchedulable
---
The three halves of a reduction, put together: the map is `Construction2.reduce`, its
correctness is `reduce_correct`, the slice it lands in is `reduce_slice`, and the time it
takes is `reduce_ramPolytime`.
-/
theorem sat34_polyReducesOn_allSchedulable :
    PolyReducesOn Lax470956.Exact34Encoding.Satisfiable
      {y | ∃ I, EncodesInstance y I ∧ I.AllSchedulable}
      Lax470956.Theorem2.BoundedSlice :=
  ⟨reduce, ramPolytime_reduce, fun x => Lax470956Proofs.Reduce.reduce_slice x,
    fun x => Lax470956Proofs.Reduce.reduce_correct x⟩

end Lax470956Proofs.Checker
