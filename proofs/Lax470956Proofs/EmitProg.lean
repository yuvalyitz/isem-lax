import Lax470956Proofs.Emit
import Lax470956Proofs.Pmax
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic

/-!
Construction 2's reduction as a word RAM program.

The program reads the two header entries, copies the clause block into an array so that
the appearance indices can be read again in each pass, and then writes the six blocks of
the instance encoding in order: the two counts, the processing times, the deadlines, the
weights, the offsets, and the eligible machines.

Each block is one counted pass over the jobs. A pass over the clause jobs recovers the
clause, the literal and the slot of job `j` by dividing `j - V` by nine and three, reads
the appearance index out of the array, and forms the deadline; the slot then selects
which of the three numbers of that literal's window the pass is writing.
-/

namespace Lax470956Proofs.EmitProg

open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer
open Lax470956.Exact34Encoding Lax470956.Construction2 Lax470956Proofs.Emit

/-! ### Expression shorthands -/

private abbrev sub (e f : Expr) : Expr := .bin .sub e f
private abbrev mul (e f : Expr) : Expr := .bin .mul e f
private abbrev dvd (e f : Expr) : Expr := .bin .div e f
private abbrev add (e f : Expr) : Expr := .bin .add e f

/-! ### The program -/

/-- Copy one entry of the clause block into the array. -/
def readBody : Com :=
  .seq (.read "v")
    (.seq (.store "a" (.var "t") (.var "v"))
      (.assign "t" (add (.var "t") (.lit 1))))

/-- Copy the whole clause block into the array. -/
def readLoop : Com :=
  .seq (.assign "t" (.lit 0)) (.while (.lt (.var "t") (.var "L")) readBody)

/-- Recover the clause, literal and slot of clause job `j`, and its deadline. -/
def decode : Com :=
  .seq (.assign "q" (sub (.var "j") (.var "V")))
  (.seq (.assign "c" (dvd (.var "q") (.lit 9)))
  (.seq (.assign "h" (dvd (sub (.var "q") (mul (.lit 9) (.var "c"))) (.lit 3)))
  (.seq (.assign "s" (sub (sub (.var "q") (mul (.lit 9) (.var "c"))) (mul (.lit 3) (.var "h"))))
  (.seq (.assign "p" (add (mul (.lit 9) (.var "c")) (mul (.lit 3) (.var "h"))))
  (.seq (.assign "k" (.get "a" (add (.var "p") (.lit 2))))
  (.seq (.assign "d" (add (mul (.lit 2) (add (.var "k") (.lit 1))) (mul (.lit 8) (.var "h"))))
  (.seq (.ite (.lt (.var "d") (.lit 2)) (.assign "d" (.lit 2)) .skip)
        (.ite (.lt (.lit 24) (.var "d")) (.assign "d" (.lit 24)) .skip))))))))

/-- Bump the job counter. -/
def bumpJ : Com := .assign "j" (add (.var "j") (.lit 1))

/-- Choose which of a literal's three processing times to write. -/
def procDispatch : Com :=
  .ite (.eq (.var "s") (.lit 0))
    (.write (.lit 1))
    (.ite (.eq (.var "s") (.lit 1))
      (.write (sub (.var "d") (.lit 1)))
      (.write (sub (.lit 25) (.var "d"))))

/-- One processing time. -/
def procBody : Com :=
  .seq (.ite (.lt (.var "j") (.var "V"))
          (.write (.lit 25))
          (.seq decode procDispatch))
    bumpJ

/-- Choose which of a literal's three deadlines to write. -/
def dueDispatch : Com :=
  .ite (.eq (.var "s") (.lit 0))
    (.write (.var "d"))
    (.ite (.eq (.var "s") (.lit 1))
      (.write (sub (.var "d") (.lit 1)))
      (.write (.lit 25)))

/-- One deadline. -/
def dueBody : Com :=
  .seq (.ite (.lt (.var "j") (.var "V"))
          (.write (.lit 25))
          (.seq decode dueDispatch))
    bumpJ

/-- One weight. -/
def wtBody : Com := .seq (.write (.lit 1)) bumpJ

/-- One offset. -/
def offBody : Com :=
  .seq (.ite (.lt (.var "V") (.var "j"))
          (.write (add (mul (.lit 2) (.var "V")) (mul (.lit 3) (sub (.var "j") (.var "V")))))
          (.write (mul (.lit 2) (.var "j"))))
    bumpJ

/-- Write the three machines of a clause job. -/
def tgtDispatch : Com :=
  .seq (.assign "b" (add (mul (.lit 2) (.var "V")) (mul (.lit 3) (.var "c"))))
    (.ite (.eq (.var "s") (.lit 0))
      (.seq (.write (add (.var "b") (.lit 1)))
      (.seq (.write (add (.var "b") (.lit 2)))
      (.seq (.assign "r" (.get "a" (.var "p")))
      (.seq (.assign "g" (.get "a" (add (.var "p") (.lit 1))))
        (.ite (.eq (.var "g") (.lit 1))
          (.write (mul (.lit 2) (.var "r")))
          (.write (add (mul (.lit 2) (.var "r")) (.lit 1))))))))
      (.seq (.write (.var "b"))
      (.seq (.write (add (.var "b") (.lit 1)))
            (.write (add (.var "b") (.lit 2))))))

/-- The eligible machines of one job. -/
def tgtBody : Com :=
  .seq (.ite (.lt (.var "j") (.var "V"))
          (.seq (.write (mul (.lit 2) (.var "j")))
                (.write (add (mul (.lit 2) (.var "j")) (.lit 1))))
          (.seq decode tgtDispatch))
    bumpJ

/-- A counted pass over the jobs. -/
def jobLoop (body : Com) (bound : String) : Com :=
  .seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var bound)) body)

/-- **The reduction.** -/
def com : Com :=
  .seq (.read "V") (.seq (.read "C") (.seq (.assign "L" (mul (.lit 9) (.var "C"))) (.seq (.assign "n" (add (.var "V") (mul (.lit 9) (.var "C")))) (.seq (.assign "M" (add (mul (.lit 2) (.var "V")) (mul (.lit 3) (.var "C")))) (.seq (.assign "N" (add (.var "n") (.lit 1))) (.seq readLoop (.seq (.write (.var "n")) (.seq (.write (.var "M")) (.seq (jobLoop procBody "n") (.seq (jobLoop dueBody "n") (.seq (jobLoop wtBody "n") (.seq (jobLoop offBody "N") ((jobLoop tgtBody "n"))))))))))))))

/-- Eighteen scalars, one array, eight temporaries. -/
def layout : Layout :=
  ⟨["V", "C", "L", "n", "M", "N", "t", "j", "v", "q", "c", "h", "s", "p", "k", "d",
    "b", "r", "g"], ["a"], 8⟩

/-- The machine program. -/
def prog : Program := compileProgram layout com

theorem com_ok : Com.Ok layout com := by
  simp [com, readLoop, readBody, jobLoop, procBody, procDispatch, dueBody, dueDispatch,
    wtBody, offBody, tgtBody, tgtDispatch, decode, bumpJ, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by simp [Layout.const]

variable (x : List ℕ)

/-! ### Sizes of a well-formed formula -/

/-- The word's length, in the names the construction uses. -/
lemma wf_length (hwf : WellFormed x) : x.length = 2 + 9 * nCla x := hwf.length_eq

/-- The variable bound, in the names the construction uses. -/
lemma wf_var_le (hwf : WellFormed x) : nVar x ≤ 3 * nCla x := hwf.var_le

/-- Every literal names a declared variable, in the names the construction uses. -/
lemma wf_litVar_lt (hwf : WellFormed x) {c h : ℕ} (hc : c < nCla x) (hh : h < 3) :
    litVar x c h < nVar x := hwf.var_lt c hc h hh

/-- The clause block is the input minus its two header entries. -/
lemma drop_length (hwf : WellFormed x) : (x.drop 2).length = 9 * nCla x := by
  have := wf_length x hwf
  simp only [List.length_drop]
  omega

lemma nJobs_le (hwf : WellFormed x) : nJobs x ≤ 12 * nCla x := by
  have := wf_var_le x hwf
  simp only [nJobs]
  omega

lemma nMach_le (hwf : WellFormed x) : nMach x ≤ 9 * nCla x := by
  have := wf_var_le x hwf
  simp only [nMach]
  omega

lemma nCla_lt (hwf : WellFormed x) : 9 * nCla x < x.length + 1 := by
  have := wf_length x hwf; omega

/-- The value bound: nothing the program forms exceeds it. -/
def bnd (x : List ℕ) : ℕ := 40 * (x.length + x.foldr max 0) + 40

lemma entry_lt_bnd {v : ℕ} (hv : v ∈ x) : v < bnd x := by
  have := Lax470956Proofs.Pmax.le_foldr_max hv
  simp only [bnd]; omega

/-! ### The copy loop -/

/-- The state of the loop that copies the clause block into the array. -/
def RInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "V" = nVar x ∧ σ.vars "C" = nCla x ∧ σ.vars "L" = 9 * nCla x ∧
    σ.vars "n" = nJobs x ∧ σ.vars "M" = nMach x ∧ σ.vars "N" = nJobs x + 1 ∧
    σ.vars "t" ≤ 9 * nCla x ∧
    (σ.arrs "a").length = 9 * nCla x ∧
    (∀ i < σ.vars "t", (σ.arrs "a").getD i 0 = (x.drop 2).getD i 0) ∧
    σ.inp = (x.drop 2).drop (σ.vars "t") ∧ σ.out = []

theorem readBody_spec (hwf : WellFormed x) :
    Spec (bnd x) (fun σ => RInv x σ ∧ σ.vars "t" < 9 * nCla x) readBody
      (fun σ σ' => RInv x σ' ∧ σ'.vars "t" = σ.vars "t" + 1) 8 := by
  refine Spec.pre (P := fun σ => RInv x σ ∧ σ.vars "t" < 9 * nCla x ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < bnd x ∧ σ.vars "t" < (σ.arrs "a").length ∧
      σ.vars "t" + 1 < bnd x) ?_ ?_
  · run_vcg
    · obtain ⟨hV, hC, hL, hn, hM, hN, hle, hlen, hcell, hinp, hout⟩ := ‹RInv x σ›
      have htlt := ‹σ.vars "t" < 9 * nCla x›
      have hidx : σ.vars "t" < (σ.arrs "a").length := by rw [hlen]; exact htlt
      simp only [RInv]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hV
      · exact hC
      · exact hL
      · exact hn
      · exact hM
      · exact hN
      · exact htlt
      · exact hlen
      · intro i hi
        rcases Nat.lt_or_ge i (σ.vars "t") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using hcell i h
        · have hie : i = σ.vars "t" := by omega
          subst hie
          rw [hinp]
          simp [List.getElem?_set, hidx, List.head?_drop]
      · rw [hinp, List.tail_drop, List.drop_drop]
      · exact hout
    · simp only [Env.setVar, if_pos rfl]
      exact ‹σ.inp.headD 0 < bnd x›
  · rintro σ ⟨hI, ht⟩
    have hlen := drop_length x hwf
    have hinp : σ.inp = (x.drop 2).drop (σ.vars "t") := hI.2.2.2.2.2.2.2.2.2.1
    have hne : σ.inp ≠ [] := by
      rw [hinp]
      intro hc
      have : ((x.drop 2).drop (σ.vars "t")).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop, hlen] at this
      omega
    refine ⟨hI, ht, hne, ?_, ?_, ?_⟩
    · have hsub : ∀ u ∈ σ.inp, u ∈ x := by
        intro u hu
        rw [hinp] at hu
        exact List.mem_of_mem_drop (List.mem_of_mem_drop hu)
      rcases hh : σ.inp with _ | ⟨u, rest⟩
      · exact absurd hh hne
      · exact entry_lt_bnd x (hsub u (by rw [hh]; exact List.mem_cons_self))
    · rw [hI.2.2.2.2.2.2.2.1]; exact ht
    · have := nCla_lt x hwf
      simp only [bnd]; omega

/-- The copy loop reads the whole clause block into the array. -/
theorem readLoop_spec (hwf : WellFormed x) :
    Spec (bnd x) (fun σ => RInv x (σ.setVar "t" 0)) readLoop
      (fun _ σ' => RInv x σ' ∧ σ'.vars "t" = 9 * nCla x) (12 * (9 * nCla x) + 6) :=
  Spec.forRangeZero "t" "L" (RInv x) (9 * nCla x) 8
    (by have := nCla_lt x hwf; simp only [bnd]; omega)
    (fun _ h => h.2.2.2.2.2.2.1) (fun _ h => h.2.2.1) (readBody_spec x hwf)

/-- When the copy loop is done the array holds the clause block. -/
theorem arr_eq (hwf : WellFormed x) {σ : Env} (h : RInv x σ)
    (ht : σ.vars "t" = 9 * nCla x) : σ.arrs "a" = x.drop 2 := by
  obtain ⟨-, -, -, -, -, -, -, hlen, hcell, -, -⟩ := h
  have hd := drop_length x hwf
  refine List.ext_getElem (by rw [hlen, hd]) ?_
  intro i h1 h2
  have hi := hcell i (by rw [ht]; rw [hlen] at h1; exact h1)
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at hi

/-! ### The passes that write the blocks -/

/-- The context each output pass runs in: the header scalars and the clause array. -/
def Ctx (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "V" = nVar x ∧ σ.vars "C" = nCla x ∧ σ.vars "L" = 9 * nCla x ∧
    σ.vars "n" = nJobs x ∧ σ.vars "M" = nMach x ∧ σ.vars "N" = nJobs x + 1 ∧
    σ.arrs "a" = x.drop 2

/-- The copy loop's exit state is the context every pass starts in. -/
theorem ctx_of_rinv (hwf : WellFormed x) {σ : Env} (h : RInv x σ)
    (ht : σ.vars "t" = 9 * nCla x) : Ctx x σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, arr_eq x hwf h ht⟩

/-- The copy loop, with its exit stated as the context the passes need. -/
theorem readLoop_spec' (hwf : WellFormed x) :
    Spec (bnd x) (fun σ => RInv x (σ.setVar "t" 0)) readLoop
      (fun _ σ' => Ctx x σ' ∧ σ'.out = [] ∧ σ'.vars "n" = nJobs x ∧
        σ'.vars "N" = nJobs x + 1) (12 * (9 * nCla x) + 6) := by
  intro σ hσ
  obtain ⟨σ', hrun, hI, ht⟩ := readLoop_spec x hwf σ hσ
  exact ⟨σ', hrun, ctx_of_rinv x hwf hI ht, hI.2.2.2.2.2.2.2.2.2.2,
    hI.2.2.2.1, hI.2.2.2.2.2.1⟩

/-- A pass in progress: the counter has written the first `j` entries of the block. -/
def BInv (x : List ℕ) (bound : String) (N : ℕ) (out0 : List ℕ) (g : ℕ → ℕ)
    (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "j" ≤ N ∧ σ.vars bound = N ∧
    σ.out = out0 ++ (List.range (σ.vars "j")).map g

/-- **A counted pass writes its block.** -/
theorem blockLoop {bd : Com} {bound : String} {N Kb : ℕ} {g : ℕ → ℕ} {out0 : List ℕ}
    (hNB : N < bnd x)
    (hbody : Spec (bnd x) (fun σ => BInv x bound N out0 g σ ∧ σ.vars "j" < N) bd
      (fun σ σ' => BInv x bound N out0 g σ' ∧ σ'.vars "j" = σ.vars "j" + 1) Kb) :
    Spec (bnd x) (fun σ => BInv x bound N out0 g (σ.setVar "j" 0))
      (jobLoop bd bound)
      (fun _ σ' => BInv x bound N out0 g σ' ∧ σ'.vars "j" = N) ((Kb + 4) * N + 6) :=
  Spec.forRangeZero "j" bound (BInv x bound N out0 g) N Kb hNB
    (fun _ h => h.2.1) (fun _ h => h.2.2.1) hbody

lemma nJobs_lt_bnd (hwf : WellFormed x) : nJobs x + 1 < bnd x := by
  have h1 := wf_length x hwf
  have h2 := nJobs_le x hwf
  simp only [bnd]; omega

/-- Writing one more entry extends the block by one. -/
lemma map_range_succ (g : ℕ → ℕ) (j : ℕ) :
    (List.range (j + 1)).map g = (List.range j).map g ++ [g j] := by
  rw [List.range_succ, List.map_append]
  rfl

/-- One more entry, with no prefix. -/
lemma out_step' {g : ℕ → ℕ} {j v : ℕ} (h : v = g j) :
    (List.range j).map g ++ [v] = (List.range (j + 1)).map g := by
  rw [map_range_succ, h]

/-! ### The weight pass -/

theorem wtBody_spec (hwf : WellFormed x) (N : ℕ) (out0 : List ℕ) (hN : N ≤ nJobs x + 1) :
    Spec (bnd x) (fun σ => BInv x "n" N out0 (fun _ => 1) σ ∧ σ.vars "j" < N) wtBody
      (fun σ σ' => BInv x "n" N out0 (fun _ => 1) σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 6 := by
  refine Spec.pre (P := fun σ => BInv x "n" N out0 (fun _ => 1) σ ∧ σ.vars "j" < N ∧
      σ.vars "j" + 1 < bnd x ∧ (1 : ℕ) < bnd x) ?_ ?_
  · run_vcg
    obtain ⟨⟨hV, hC, hL, hn, hM, hN', harr⟩, hle, hb, hout⟩ := ‹BInv x "n" N out0 (fun _ => 1) σ›
    have hjlt := ‹σ.vars "j" < N›
    simp only [BInv, Ctx]
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩ <;> simp
    · exact hV
    · exact hC
    · exact hL
    · exact hn
    · exact hM
    · exact hN'
    · exact harr
    · omega
    · exact hb
    · rw [hout]
      simp [List.replicate_succ', List.append_assoc]
  · rintro σ ⟨hI, hj⟩
    have hb := nJobs_lt_bnd x hwf
    exact ⟨hI, hj, by omega, by omega⟩

theorem wtLoop_spec (hwf : WellFormed x) (out0 : List ℕ) :
    Spec (bnd x) (fun σ => BInv x "n" (nJobs x) out0 (fun _ => 1) (σ.setVar "j" 0))
      (jobLoop wtBody "n")
      (fun _ σ' => BInv x "n" (nJobs x) out0 (fun _ => 1) σ' ∧ σ'.vars "j" = nJobs x)
      (10 * nJobs x + 6) :=
  blockLoop x (by have := nJobs_lt_bnd x hwf; omega)
    (wtBody_spec x hwf (nJobs x) out0 (by omega))

/-! ### The offset pass -/

lemma off_lt_bnd (hwf : WellFormed x) {j : ℕ} (hj : j ≤ nJobs x) :
    2 * nVar x + 3 * (j - nVar x) + 1 < bnd x := by
  have h1 := wf_length x hwf
  have h2 := nJobs_le x hwf
  have h3 := wf_var_le x hwf
  simp only [bnd]; omega

lemma two_mul_lt_bnd (hwf : WellFormed x) {j : ℕ} (hj : j ≤ nJobs x) : 2 * j + 1 < bnd x := by
  have h1 := wf_length x hwf
  have h2 := nJobs_le x hwf
  simp only [bnd]; omega

theorem offBody_spec (hwf : WellFormed x) (out0 : List ℕ) :
    Spec (bnd x)
      (fun σ => BInv x "N" (nJobs x + 1) out0 (offOf x) σ ∧ σ.vars "j" < nJobs x + 1)
      offBody
      (fun σ σ' => BInv x "N" (nJobs x + 1) out0 (offOf x) σ' ∧
        σ'.vars "j" = σ.vars "j" + 1) 20 := by
  refine Spec.pre (P := fun σ => BInv x "N" (nJobs x + 1) out0 (offOf x) σ ∧
      σ.vars "j" < nJobs x + 1 ∧ σ.vars "j" + 1 < bnd x ∧
      2 * σ.vars "V" + 3 * (σ.vars "j" - σ.vars "V") + 1 < bnd x ∧
      2 * σ.vars "j" + 1 < bnd x) ?_ ?_
  · run_vcg
    all_goals
      obtain ⟨⟨hV, hC, hL, hn, hM, hN', harr⟩, hle, hb, hout⟩ :=
        ‹BInv x "N" (nJobs x + 1) out0 (offOf x) σ›
    all_goals have hjlt := ‹σ.vars "j" < nJobs x + 1›
    all_goals have hbb := ‹2 * σ.vars "V" + 3 * (σ.vars "j" - σ.vars "V") + 1 < bnd x›
    all_goals have hbc := ‹2 * σ.vars "j" + 1 < bnd x›
    all_goals try simp only [BInv, Ctx]
    all_goals try refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    all_goals try simp
    all_goals first
      | exact hV | exact hC | exact hL | exact hn | exact hM | exact hN' | exact harr
      | omega | exact hb | (simp only [bnd]; omega)
      | (rw [hout, map_range_succ, ← List.append_assoc]
         congr 2
         simp only [offOf]
         split <;> omega)
  · rintro σ ⟨hI, hj⟩
    have hb := nJobs_lt_bnd x hwf
    have hV : σ.vars "V" = nVar x := hI.1.1
    refine ⟨hI, hj, by omega, ?_, ?_⟩
    · rw [hV]; exact off_lt_bnd x hwf (by omega)
    · exact two_mul_lt_bnd x hwf (by omega)

theorem offLoop_spec (hwf : WellFormed x) (out0 : List ℕ) :
    Spec (bnd x)
      (fun σ => BInv x "N" (nJobs x + 1) out0 (offOf x) (σ.setVar "j" 0))
      (jobLoop offBody "N")
      (fun _ σ' => BInv x "N" (nJobs x + 1) out0 (offOf x) σ' ∧
        σ'.vars "j" = nJobs x + 1)
      (24 * (nJobs x + 1) + 6) :=
  blockLoop x (nJobs_lt_bnd x hwf) (offBody_spec x hwf out0)

/-! ### Decoding a clause job -/

lemma small_lt_bnd (hwf : WellFormed x) :
    40 * nCla x + 40 * nVar x + 64 < bnd x := by
  have h1 := wf_length x hwf
  have h2 := wf_var_le x hwf
  simp only [bnd]; omega

/-- The same read, after the drop has been pushed into the index. -/
lemma x_read_eq (a : ℕ) :
    x[2 + (9 * (a / 9) + 3 * ((a - 9 * (a / 9)) / 3) + 2)]?.getD 0
      = litApp x (cOf a) (hOf a) := by
  simp only [litApp, cOf, hOf, List.getD_eq_getElem?_getD]
  congr 2
  omega

/-- What `decode` leaves behind. -/
def Dec (x : List ℕ) (j : ℕ) (outj : List ℕ) (σ' : Env) : Prop :=
  Ctx x σ' ∧ σ'.vars "j" = j ∧ σ'.out = outj ∧
    σ'.vars "c" = cOf (j - nVar x) ∧ σ'.vars "h" = hOf (j - nVar x) ∧
    σ'.vars "s" = sOf (j - nVar x) ∧
    σ'.vars "p" = 9 * cOf (j - nVar x) + 3 * hOf (j - nVar x) ∧
    σ'.vars "d" = dl x (cOf (j - nVar x)) (hOf (j - nVar x))

/-- Everything `decode` needs to know, gathered once. -/
def DecPre (x : List ℕ) (j : ℕ) (outj : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "j" = j ∧ σ.out = outj ∧
    σ.vars "V" = nVar x ∧ σ.arrs "a" = x.drop 2 ∧
    (σ.arrs "a").length = 9 * nCla x ∧
    40 * nCla x + 40 * nVar x + 64 < bnd x ∧ σ.vars "j" < bnd x ∧ σ.vars "V" < bnd x ∧
    nVar x ≤ j ∧ j - nVar x < 9 * nCla x ∧
    cOf (j - nVar x) < nCla x ∧ hOf (j - nVar x) < 3 ∧ sOf (j - nVar x) < 3 ∧
    litApp x (cOf (j - nVar x)) (hOf (j - nVar x)) < 4

theorem decPre_of (hwf : WellFormed x) {j : ℕ} {outj : List ℕ} {σ : Env}
    (hctx : Ctx x σ) (hjj : σ.vars "j" = j) (hout : σ.out = outj)
    (hVj : nVar x ≤ j) (hjn : j < nJobs x) : DecPre x j outj σ := by
  have hnj : nJobs x = nVar x + 9 * nCla x := rfl
  have hq : j - nVar x < 9 * nCla x := by omega
  have hc3 : cOf (j - nVar x) < nCla x := by simp only [cOf]; omega
  have hh3 : hOf (j - nVar x) < 3 := by simp only [hOf]; omega
  have hs3 : sOf (j - nVar x) < 3 := by simp only [sOf]; omega
  have harr : σ.arrs "a" = x.drop 2 := hctx.2.2.2.2.2.2
  have hsm := small_lt_bnd x hwf
  refine ⟨hctx, hjj, hout, hctx.1, harr, by rw [harr]; exact drop_length x hwf, hsm,
    by rw [hjj]; omega, by rw [hctx.1]; omega, hVj, hq, hc3, hh3, hs3,
    hwf.app_lt _ hc3 _ hh3⟩

set_option maxHeartbeats 2000000 in
theorem decode_spec (hwf : WellFormed x) (j : ℕ) (outj : List ℕ) :
    Spec (bnd x) (DecPre x j outj) decode (fun _ σ' => Dec x j outj σ') 64 := by
  unfold DecPre
  run_vcg
  all_goals obtain ⟨hcV, hcC, hcL, hcn, hcM, hcN, hcA⟩ := ‹Ctx x σ›
  all_goals have hjj : σ.vars "j" = j := ‹σ.vars "j" = j›
  all_goals have hVn : σ.vars "V" = nVar x := ‹σ.vars "V" = nVar x›
  all_goals have harr : σ.arrs "a" = x.drop 2 := ‹σ.arrs "a" = x.drop 2›
  all_goals have hh3 : hOf (j - nVar x) < 3 := ‹hOf (j - nVar x) < 3›
  all_goals have hk4 : litApp x (cOf (j - nVar x)) (hOf (j - nVar x)) < 4 :=
    ‹litApp x (cOf (j - nVar x)) (hOf (j - nVar x)) < 4›
  all_goals try simp only [Dec, Ctx]
  all_goals try simp_all [x_read_eq, cOf, hOf, sOf]
  all_goals try and_intros
  all_goals first
    | assumption
    | omega
    | (simp only [dl]; omega)
    | (simp [dl]; omega)
    | (simp_all [dl]; omega)

/-! ### What the clause-job passes write -/

lemma procOf_lt {j : ℕ} (hj : j < nVar x) : procOf x j = 25 := by
  simp only [procOf, if_pos hj]

lemma dueOf_lt {j : ℕ} (hj : j < nVar x) : dueOf x j = 25 := by
  simp only [dueOf, if_pos hj]

lemma procOf_ge {j : ℕ} (hj : ¬ j < nVar x) :
    procOf x j = (if sOf (j - nVar x) = 0 then 1
      else if sOf (j - nVar x) = 1 then dl x (cOf (j - nVar x)) (hOf (j - nVar x)) - 1
      else 25 - dl x (cOf (j - nVar x)) (hOf (j - nVar x))) := by
  simp only [procOf, if_neg hj]
  rcases hv : sOf (j - nVar x) with _ | _ | k <;> simp [hv]

lemma dueOf_ge {j : ℕ} (hj : ¬ j < nVar x) :
    dueOf x j = (if sOf (j - nVar x) = 0 then dl x (cOf (j - nVar x)) (hOf (j - nVar x))
      else if sOf (j - nVar x) = 1 then dl x (cOf (j - nVar x)) (hOf (j - nVar x)) - 1
      else 25) := by
  simp only [dueOf, if_neg hj]
  rcases hv : sOf (j - nVar x) with _ | _ | k <;> simp [hv]

/-- What `decode` leaves behind, read off the state itself rather than off the state it
started in. A following phase can then be specified without mentioning the
intermediate state. -/
def DecAt (x : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ nVar x ≤ σ.vars "j" ∧ σ.vars "j" < nJobs x ∧
    σ.vars "s" = sOf (σ.vars "j" - nVar x) ∧
    σ.vars "d" = dl x (cOf (σ.vars "j" - nVar x)) (hOf (σ.vars "j" - nVar x)) ∧
    σ.vars "c" = cOf (σ.vars "j" - nVar x) ∧
    σ.vars "h" = hOf (σ.vars "j" - nVar x) ∧
    σ.vars "p" = 9 * cOf (σ.vars "j" - nVar x) + 3 * hOf (σ.vars "j" - nVar x) ∧
    cOf (σ.vars "j" - nVar x) < nCla x ∧ hOf (σ.vars "j" - nVar x) < 3 ∧
    litVar x (cOf (σ.vars "j" - nVar x)) (hOf (σ.vars "j" - nVar x)) < nVar x ∧
    (σ.arrs "a").length = 9 * nCla x ∧
    40 * nCla x + 40 * nVar x + 64 < bnd x

/-- `decode_spec` in the form the walk composes with. -/
theorem decode_spec' (hwf : WellFormed x) :
    Spec (bnd x) (fun σ => DecPre x (σ.vars "j") σ.out σ) decode
      (fun σ σ' => DecAt x σ' ∧ σ'.vars "j" = σ.vars "j" ∧ σ'.out = σ.out) 64 := by
  intro σ hσ
  obtain ⟨σ', hrun, hctx, hj, hout, hc, hh, hs, hp, hd⟩ :=
    decode_spec x hwf (σ.vars "j") σ.out σ hσ
  obtain ⟨-, -, -, -, -, hlen, hsm, -, -, hVj, hqlt, hc3, hh3, -, -⟩ := hσ
  have hnj : nJobs x = nVar x + 9 * nCla x := rfl
  have hlv : litVar x (cOf (σ.vars "j" - nVar x)) (hOf (σ.vars "j" - nVar x)) < nVar x :=
    hwf.var_lt _ hc3 _ hh3
  have hlen' : (σ'.arrs "a").length = 9 * nCla x := by
    rw [hctx.2.2.2.2.2.2]; exact drop_length x hwf
  refine ⟨σ', hrun, ⟨hctx, by rw [hj]; exact hVj, by rw [hj]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hlen', hsm⟩, hj, hout⟩
  · rw [hj]; exact hs
  · rw [hj]; exact hd
  · rw [hj]; exact hc
  · rw [hj]; exact hh
  · rw [hj]; exact hp
  · rw [hj]; exact hc3
  · rw [hj]; exact hh3
  · rw [hj]; exact hlv

/-- Choosing the processing time. -/
theorem procDispatch_spec (hwf : WellFormed x) :
    Spec (bnd x) (DecAt x) procDispatch
      (fun σ σ' => σ' = { σ with out := σ.out ++ [procOf x (σ.vars "j")] }) 12 := by
  refine Spec.pre (P := fun σ => DecAt x σ ∧ σ.vars "s" < 3 ∧ σ.vars "d" ≤ 24 ∧
      64 < bnd x) ?_ ?_
  · run_vcg
    all_goals obtain ⟨-, hVj, -, hs, hd, -, -, -, -, -, -, -, -⟩ := ‹DecAt x σ›
    all_goals have hs3 := ‹σ.vars "s" < 3›
    all_goals have hd24 := ‹σ.vars "d" ≤ 24›
    all_goals have hb64 := ‹64 < bnd x›
    all_goals try simp
    all_goals try (rw [procOf_ge x (by omega)])
    all_goals first
      | omega
      | (rw [← hs, ← hd]; split_ifs <;> omega)
  · rintro σ hD
    have hs3 : σ.vars "s" < 3 := by rw [hD.2.2.2.1]; simp only [sOf]; omega
    have hd24 : σ.vars "d" ≤ 24 := by rw [hD.2.2.2.2.1]; exact dl_le x _ _
    exact ⟨hD, hs3, hd24, by have := hD.2.2.2.2.2.2.2.2.2.2.2.2; omega⟩

/-- Choosing the deadline. -/
theorem dueDispatch_spec (hwf : WellFormed x) :
    Spec (bnd x) (DecAt x) dueDispatch
      (fun σ σ' => σ' = { σ with out := σ.out ++ [dueOf x (σ.vars "j")] }) 12 := by
  refine Spec.pre (P := fun σ => DecAt x σ ∧ σ.vars "s" < 3 ∧ σ.vars "d" ≤ 24 ∧
      64 < bnd x) ?_ ?_
  · run_vcg
    all_goals obtain ⟨-, hVj, -, hs, hd, -, -, -, -, -, -, -, -⟩ := ‹DecAt x σ›
    all_goals have hs3 := ‹σ.vars "s" < 3›
    all_goals have hd24 := ‹σ.vars "d" ≤ 24›
    all_goals have hb64 := ‹64 < bnd x›
    all_goals try simp
    all_goals try (rw [dueOf_ge x (by omega)])
    all_goals first
      | omega
      | (rw [← hs, ← hd]; split_ifs <;> omega)
  · rintro σ hD
    have hs3 : σ.vars "s" < 3 := by rw [hD.2.2.2.1]; simp only [sOf]; omega
    have hd24 : σ.vars "d" ≤ 24 := by rw [hD.2.2.2.2.1]; exact dl_le x _ _
    exact ⟨hD, hs3, hd24, by have := hD.2.2.2.2.2.2.2.2.2.2.2.2; omega⟩

/-! ### The processing-time and deadline passes -/

theorem procBody_spec (hwf : WellFormed x) (out0 : List ℕ) :
    Spec (bnd x)
      (fun σ => BInv x "n" (nJobs x) out0 (procOf x) σ ∧ σ.vars "j" < nJobs x)
      procBody
      (fun σ σ' => BInv x "n" (nJobs x) out0 (procOf x) σ' ∧
        σ'.vars "j" = σ.vars "j" + 1) 100 := by
  refine Spec.pre (P := fun σ => BInv x "n" (nJobs x) out0 (procOf x) σ ∧
      σ.vars "j" < nJobs x ∧ 40 * nCla x + 40 * nVar x + 64 < bnd x) ?_ ?_
  · run_vcg [decode_spec' x hwf, procDispatch_spec x hwf]
    all_goals have hbi := ‹BInv x "n" (nJobs x) out0 (procOf x) σ›
    all_goals have hjn := ‹σ.vars "j" < nJobs x›
    all_goals have hsm := ‹40 * nCla x + 40 * nVar x + 64 < bnd x›
    all_goals have hV : σ.vars "V" = nVar x := hbi.1.1
    all_goals have hnjeq : nJobs x = nVar x + 9 * nCla x := rfl
    all_goals first
      | assumption
      | omega
      | (exact decPre_of x hwf hbi.1 rfl rfl
          (by have := ‹¬σ.vars "j" < σ.vars "V"›; omega) hjn)
      | (simp_all [BInv, Ctx, DecAt]
         try and_intros
         all_goals first
           | assumption
           | omega
           | (simp only [cOf]; omega)
           | (simp only [hOf]; omega)
           | (have := wf_length x hwf; omega)
           | (exact wf_litVar_lt x hwf (by first | assumption | (simp only [cOf]; omega))
                (by first | assumption | (simp only [hOf]; omega)))
           | (refine out_step' ?_
              first | exact (procOf_lt x (by omega)).symm | rfl))
  · rintro σ ⟨hI, hj⟩
    exact ⟨hI, hj, small_lt_bnd x hwf⟩

theorem dueBody_spec (hwf : WellFormed x) (out0 : List ℕ) :
    Spec (bnd x)
      (fun σ => BInv x "n" (nJobs x) out0 (dueOf x) σ ∧ σ.vars "j" < nJobs x)
      dueBody
      (fun σ σ' => BInv x "n" (nJobs x) out0 (dueOf x) σ' ∧
        σ'.vars "j" = σ.vars "j" + 1) 100 := by
  refine Spec.pre (P := fun σ => BInv x "n" (nJobs x) out0 (dueOf x) σ ∧
      σ.vars "j" < nJobs x ∧ 40 * nCla x + 40 * nVar x + 64 < bnd x) ?_ ?_
  · run_vcg [decode_spec' x hwf, dueDispatch_spec x hwf]
    all_goals have hbi := ‹BInv x "n" (nJobs x) out0 (dueOf x) σ›
    all_goals have hjn := ‹σ.vars "j" < nJobs x›
    all_goals have hsm := ‹40 * nCla x + 40 * nVar x + 64 < bnd x›
    all_goals have hV : σ.vars "V" = nVar x := hbi.1.1
    all_goals have hnjeq : nJobs x = nVar x + 9 * nCla x := rfl
    all_goals first
      | assumption
      | omega
      | (exact decPre_of x hwf hbi.1 rfl rfl
          (by have := ‹¬σ.vars "j" < σ.vars "V"›; omega) hjn)
      | (simp_all [BInv, Ctx, DecAt]
         try and_intros
         all_goals first
           | assumption
           | omega
           | (simp only [cOf]; omega)
           | (simp only [hOf]; omega)
           | (have := wf_length x hwf; omega)
           | (exact wf_litVar_lt x hwf (by first | assumption | (simp only [cOf]; omega))
                (by first | assumption | (simp only [hOf]; omega)))
           | (refine out_step' ?_
              first | exact (dueOf_lt x (by omega)).symm | rfl))
  · rintro σ ⟨hI, hj⟩
    exact ⟨hI, hj, small_lt_bnd x hwf⟩

theorem procLoop_spec (hwf : WellFormed x) (out0 : List ℕ) :
    Spec (bnd x) (fun σ => BInv x "n" (nJobs x) out0 (procOf x) (σ.setVar "j" 0))
      (jobLoop procBody "n")
      (fun _ σ' => BInv x "n" (nJobs x) out0 (procOf x) σ' ∧ σ'.vars "j" = nJobs x)
      (104 * nJobs x + 6) :=
  blockLoop x (by have := nJobs_lt_bnd x hwf; omega) (procBody_spec x hwf out0)

theorem dueLoop_spec (hwf : WellFormed x) (out0 : List ℕ) :
    Spec (bnd x) (fun σ => BInv x "n" (nJobs x) out0 (dueOf x) (σ.setVar "j" 0))
      (jobLoop dueBody "n")
      (fun _ σ' => BInv x "n" (nJobs x) out0 (dueOf x) σ' ∧ σ'.vars "j" = nJobs x)
      (104 * nJobs x + 6) :=
  blockLoop x (by have := nJobs_lt_bnd x hwf; omega) (dueBody_spec x hwf out0)

/-! ### The target pass -/

lemma flatMap_range_succ (g : ℕ → List ℕ) (j : ℕ) :
    (List.range (j + 1)).flatMap g = (List.range j).flatMap g ++ g j := by
  rw [List.range_succ, List.flatMap_append]
  simp

lemma eligOf_lt {j : ℕ} (hj : j < nVar x) : eligOf x j = [2 * j, 2 * j + 1] := by
  simp only [eligOf, if_pos hj]

lemma eligOf_ge {j : ℕ} (hj : ¬ j < nVar x) :
    eligOf x j = (if sOf (j - nVar x) = 0 then
        [2 * nVar x + 3 * cOf (j - nVar x) + 1, 2 * nVar x + 3 * cOf (j - nVar x) + 2,
         2 * litVar x (cOf (j - nVar x)) (hOf (j - nVar x)) +
           (if litSign x (cOf (j - nVar x)) (hOf (j - nVar x)) = 1 then 0 else 1)]
      else [2 * nVar x + 3 * cOf (j - nVar x), 2 * nVar x + 3 * cOf (j - nVar x) + 1,
            2 * nVar x + 3 * cOf (j - nVar x) + 2]) := by
  simp only [eligOf, if_neg hj]
  rcases hv : sOf (j - nVar x) with _ | k <;> simp [hv]

lemma x_read_var (c h : ℕ) : x[2 + (9 * c + 3 * h)]?.getD 0 = litVar x c h := by
  simp only [litVar, List.getD_eq_getElem?_getD]
  congr 2
  omega

lemma x_read_sign (c h : ℕ) : x[2 + (9 * c + 3 * h + 1)]?.getD 0 = litSign x c h := by
  simp only [litSign, List.getD_eq_getElem?_getD]
  congr 2
  omega

lemma litSign_lt_bnd (hwf : WellFormed x) {c h : ℕ} (hc : c < nCla x) (hh : h < 3) :
    litSign x c h < bnd x := by
  have hlen := wf_length x hwf
  have hlt : 2 + 9 * c + 3 * h + 1 < x.length := by omega
  have : litSign x c h = x[2 + 9 * c + 3 * h + 1] := by
    rw [litSign, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rfl
  rw [this]
  exact entry_lt_bnd x (List.getElem_mem hlt)

/-- A pass in progress, writing a variable number of entries per job. -/
def BInvL (x : List ℕ) (bound : String) (N : ℕ) (out0 : List ℕ) (g : ℕ → List ℕ)
    (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "j" ≤ N ∧ σ.vars bound = N ∧
    σ.out = out0 ++ (List.range (σ.vars "j")).flatMap g

/-- **A counted pass writes its variable-length block.** -/
theorem blockLoopL {bd : Com} {bound : String} {N Kb : ℕ} {g : ℕ → List ℕ} {out0 : List ℕ}
    (hNB : N < bnd x)
    (hbody : Spec (bnd x) (fun σ => BInvL x bound N out0 g σ ∧ σ.vars "j" < N) bd
      (fun σ σ' => BInvL x bound N out0 g σ' ∧ σ'.vars "j" = σ.vars "j" + 1) Kb) :
    Spec (bnd x) (fun σ => BInvL x bound N out0 g (σ.setVar "j" 0))
      (jobLoop bd bound)
      (fun _ σ' => BInvL x bound N out0 g σ' ∧ σ'.vars "j" = N) ((Kb + 4) * N + 6) :=
  Spec.forRangeZero "j" bound (BInvL x bound N out0 g) N Kb hNB
    (fun _ h => h.2.1) (fun _ h => h.2.2.1) hbody

/-- Writing the three machines of a clause job. -/
theorem tgtDispatch_spec (hwf : WellFormed x) :
    Spec (bnd x) (DecAt x) tgtDispatch
      (fun σ σ' => σ'.out = σ.out ++ eligOf x (σ.vars "j") ∧ Ctx x σ' ∧
        σ'.vars "j" = σ.vars "j") 40 := by
  refine Spec.pre (P := fun σ => DecAt x σ ∧ σ.vars "s" < 3 ∧
      2 * nVar x + 3 * cOf (σ.vars "j" - nVar x) + 2 < bnd x ∧
      litSign x (cOf (σ.vars "j" - nVar x)) (hOf (σ.vars "j" - nVar x)) < bnd x ∧
      2 * litVar x (cOf (σ.vars "j" - nVar x)) (hOf (σ.vars "j" - nVar x)) + 1 < bnd x ∧
      64 < bnd x) ?_ ?_
  · run_vcg
    all_goals obtain ⟨hctx, hVj, -, hs, -, hc, hh, hp, hc3, hh3, hlv, hlen, hsm⟩ :=
      ‹DecAt x σ›
    all_goals have hs3 := ‹σ.vars "s" < 3›
    all_goals try rw [eligOf_ge x (by omega)]
    all_goals try simp_all [Ctx, x_read_var, x_read_sign]
    all_goals try and_intros
    all_goals first
      | assumption
      | omega
      | rfl
      | (split_ifs <;> simp_all <;> omega)
      | (simp only [x_read_var, x_read_sign]
         split_ifs <;> simp_all <;> omega)
      | (simp only [x_read_var, x_read_sign]; omega)
  · rintro σ hD
    obtain ⟨hctx, hVj, hjn, hs, hd, hc, hh, hp, hc3, hh3, hlv, hlen, hsm⟩ := hD
    refine ⟨⟨hctx, hVj, hjn, hs, hd, hc, hh, hp, hc3, hh3, hlv, hlen, hsm⟩, ?_, by omega,
      litSign_lt_bnd x hwf hc3 hh3, by omega, by omega⟩
    rw [hs]; simp only [sOf]; omega

lemma outL_step' {g : ℕ → List ℕ} {j : ℕ} {l : List ℕ} (h : l = g j) :
    (List.range j).flatMap g ++ l = (List.range (j + 1)).flatMap g := by
  rw [flatMap_range_succ, h]

theorem tgtBody_spec (hwf : WellFormed x) (out0 : List ℕ) :
    Spec (bnd x)
      (fun σ => BInvL x "n" (nJobs x) out0 (eligOf x) σ ∧ σ.vars "j" < nJobs x)
      tgtBody
      (fun σ σ' => BInvL x "n" (nJobs x) out0 (eligOf x) σ' ∧
        σ'.vars "j" = σ.vars "j" + 1) 120 := by
  refine Spec.pre (P := fun σ => BInvL x "n" (nJobs x) out0 (eligOf x) σ ∧
      σ.vars "j" < nJobs x ∧ 40 * nCla x + 40 * nVar x + 64 < bnd x) ?_ ?_
  · run_vcg [decode_spec' x hwf, tgtDispatch_spec x hwf]
    all_goals have hbi := ‹BInvL x "n" (nJobs x) out0 (eligOf x) σ›
    all_goals have hjn := ‹σ.vars "j" < nJobs x›
    all_goals have hsm := ‹40 * nCla x + 40 * nVar x + 64 < bnd x›
    all_goals have hV : σ.vars "V" = nVar x := hbi.1.1
    all_goals have hnjeq : nJobs x = nVar x + 9 * nCla x := rfl
    all_goals have hvle := wf_var_le x hwf
    all_goals first
      | assumption
      | omega
      | (exact decPre_of x hwf hbi.1 rfl rfl
          (by have := ‹¬σ.vars "j" < σ.vars "V"›; omega) hjn)
      | (simp_all [BInvL, Ctx, DecAt]
         try and_intros
         all_goals first
           | assumption
           | omega
           | (simp only [cOf]; omega)
           | (simp only [hOf]; omega)
           | (have := wf_length x hwf; omega)
           | (exact wf_litVar_lt x hwf (by first | assumption | (simp only [cOf]; omega))
                (by first | assumption | (simp only [hOf]; omega)))
           | (refine outL_step' ?_
              first | exact (eligOf_lt x (by omega)).symm | rfl))
  · rintro σ ⟨hI, hj⟩
    exact ⟨hI, hj, small_lt_bnd x hwf⟩

theorem tgtLoop_spec (hwf : WellFormed x) (out0 : List ℕ) :
    Spec (bnd x) (fun σ => BInvL x "n" (nJobs x) out0 (eligOf x) (σ.setVar "j" 0))
      (jobLoop tgtBody "n")
      (fun _ σ' => BInvL x "n" (nJobs x) out0 (eligOf x) σ' ∧ σ'.vars "j" = nJobs x)
      (124 * nJobs x + 6) :=
  blockLoopL x (by have := nJobs_lt_bnd x hwf; omega) (tgtBody_spec x hwf out0)

/-! ### The whole program -/

/-- The array lengths the program needs: one cell per entry of the clause block. -/
def extOf (x : List ℕ) : String → ℕ := fun a => if a = "a" then 9 * nCla x else 0

/-- A well-formed word is its two header entries followed by the clause block. -/
theorem head_shape (hwf : WellFormed x) : x = nVar x :: nCla x :: x.drop 2 := by
  have hlen := wf_length x hwf
  rcases x with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at hlen; omega
  · simp at hlen; omega
  · rfl

/-- The cost of the whole program. -/
def Kcost (x : List ℕ) : ℕ := 108 * nCla x + 366 * nJobs x + 88

/-- The header of the emitted word, and the prefixes each pass starts from. -/
def pre0 (x : List ℕ) : List ℕ := [nJobs x, nMach x]
def pre1 (x : List ℕ) : List ℕ := pre0 x ++ procBlock x
def pre2 (x : List ℕ) : List ℕ := pre1 x ++ dueBlock x
def pre3 (x : List ℕ) : List ℕ := pre2 x ++ wtBlock x
def pre4 (x : List ℕ) : List ℕ := pre3 x ++ offBlock x

theorem com_spec (hwf : WellFormed x) :
    Spec (bnd x)
      (fun σ => σ.inp = nVar x :: nCla x :: x.drop 2 ∧ σ.out = [] ∧
        (σ.arrs "a").length = 9 * nCla x ∧
        40 * nCla x + 40 * nVar x + 64 < bnd x)
      com (fun _ σ' => σ'.out = emit x) (108 * nCla x + 366 * nJobs x + 88) := by
  run_vcg [readLoop_spec' x hwf, procLoop_spec x hwf (pre0 x), dueLoop_spec x hwf (pre1 x),
    wtLoop_spec x hwf (pre2 x), offLoop_spec x hwf (pre3 x), tgtLoop_spec x hwf (pre4 x)]
  all_goals have hinp : σ.inp = nVar x :: nCla x :: x.drop 2 :=
    ‹σ.inp = nVar x :: nCla x :: x.drop 2›
  all_goals have hout0 : σ.out = [] := ‹σ.out = []›
  all_goals have halen : (σ.arrs "a").length = 9 * nCla x := ‹(σ.arrs "a").length = 9 * nCla x›
  all_goals have hsm := ‹40 * nCla x + 40 * nVar x + 64 < bnd x›
  all_goals have hnj : nJobs x = nVar x + 9 * nCla x := rfl
  all_goals have hnm : nMach x = 2 * nVar x + 3 * nCla x := rfl
  all_goals have hdl := drop_length x hwf
  all_goals try simp only [RInv, Ctx, BInv, BInvL] at *
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

/-- The program solves the problem in IMP+. -/
theorem solves :
    Solves layout com Formulas emit bnd (fun x => 108 * nCla x + 366 * nJobs x + 88) where
  ok := com_ok
  inp := fun x _ v hv => entry_lt_bnd x hv
  run := by
    intro x hwf
    have hpre : (initEnv (extOf x) x).inp = nVar x :: nCla x :: x.drop 2 ∧
        (initEnv (extOf x) x).out = [] ∧
        ((initEnv (extOf x) x).arrs "a").length = 9 * nCla x ∧
        40 * nCla x + 40 * nVar x + 64 < bnd x := by
      refine ⟨?_, rfl, ?_, small_lt_bnd x hwf⟩
      · show x = _
        exact head_shape x hwf
      · simp [initEnv, extOf]
    obtain ⟨σ', hrun, hout⟩ := com_spec x hwf _ hpre
    exact ⟨extOf x, σ', hrun, hout⟩

/-- **Construction 2's reduction, end to end.** The compiled program writes the word the
reduction emits within `5881 · (|x| + 1)` instructions, at every word length at which the
formula's entries fit. -/
theorem prog_computesInTime (w : ℕ) :
    ComputesInTime w prog
      {y | y ∈ Formulas ∧ Lax470956.ParameterizedComplexity.Fits 5881 w y}
      emit (fun y => 5881 * (y.length + 1)) := by
  have hs : Solves layout com {y | y ∈ Formulas ∧ Lax470956.ParameterizedComplexity.Fits 5881 w y}
      emit bnd (fun y => 108 * nCla y + 366 * nJobs y + 88) :=
    ⟨solves.ok, fun y hy => solves.inp y hy.1, fun y hy => solves.run y hy.1⟩
  refine computesInTime_of_solves hs (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨hwf, hfits⟩ := hy
    have hlen := wf_length y hwf
    have hne : nVar y ∈ y := by
      rw [head_shape y hwf]; exact List.mem_cons_self
    have hbig : 5881 * (y.length + (y.foldr max 0) + 1) ≤ 2 ^ w := by
      rcases Lax470956Proofs.Pmax.foldr_max_mem_or_zero y with hm | hm
      · exact hfits _ hm
      · rw [hm]
        have := hfits _ hne
        omega
    refine fitsWords_of_max_le (by simp only [bnd]; omega) ?_
    simp only [Layout.span, layout, List.length_cons, List.length_nil, bnd, max_le_iff]
    omega
  · obtain ⟨hwf, -⟩ := hy
    have hlen := wf_length y hwf
    have hjl := nJobs_le y hwf
    rw [const_eq]
    omega

/--
---
conclusion: Lax470956.Construction2.emit_computesInTime
---
The program reads the two header entries, copies the clause block into an array, and
writes the six blocks of the encoding in order. The copy costs `12` per entry; the three
passes that decode a clause job cost `104`, `104` and `124` per job, the weights `10`,
the offsets `24`; and the compiler charges ten machine instructions per unit of IMP+
cost. With `V ≤ 3C` the number of jobs is at most `12C` and the word's length is
`2 + 9C`, so the whole is linear in the length of the input, and `5881 · (|x| + 1)`
covers it.

The bound on the values is the length of the word plus its largest entry: every number
the program forms is an entry it read, a count of them, or a machine index, and the
machine indices are bounded by `2V + 3C`.
-/
theorem emit_computesInTime :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {y | WellFormed y ∧ Lax470956.ParameterizedComplexity.Fits c w y}
        emit (fun y => c * (y.length + 1)) :=
  ⟨prog, 5881, fun w => prog_computesInTime w⟩

end Lax470956Proofs.EmitProg
