import Lax470956.SchedulingProblems
import Lax808846Proofs.Transfer
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.List.GetD

/-!
The largest processing time, as a word RAM program.

`SchedulingProblems.pmaxOf` is the parameter half of the combined parameter of
Theorem 3, and a program deciding that problem has to obtain it. This file is that
program: it reads the two header entries, then the processing-time block, keeping the
largest entry seen, and writes it.

The program is written in IMP+ and compiled; the cost is `15` per processing time plus
`12`, so the machine runs within `10 · (15 |x| + 12) + 1` instructions — linear in the
length of the word, with the constant written out. The value bound is `x.sum + 2`: every
quantity the program forms is an entry of the input or a count of them.
-/

namespace Lax470956Proofs.Pmax

open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer

/-! ### The Program -/

/-- `i < n`, the loop condition. -/
def cond : Cond := .lt (.var "i") (.var "n")

/-- Read the next processing time, keep it if it beats the best so far, count it. -/
def body : Com :=
  .seq (.read "v")
    (.seq (.ite (.lt (.var "best") (.var "v")) (.assign "best" (.var "v")) .skip)
      (.assign "i" (.add (.var "i") (.lit 1))))

/-- Read the two header entries, then the `n` processing times, then write the
largest. -/
def com : Com :=
  .seq (.read "n")
    (.seq (.read "m")
      (.seq (.assign "i" (.lit 0))
        (.seq (.assign "best" (.lit 0))
          (.seq (.while cond body) (.write (.var "best"))))))

/-- Five scalars, no arrays, two temporaries. -/
def layout : Layout := ⟨["n", "m", "i", "best", "v"], [], 2⟩

/-- The machine program. -/
def prog : Program := compileProgram layout com

/-! ### The Domain, and What the Program Computes -/

/-- Words shaped like an instance encoding: the job count, the machine count, then that
many processing times, then whatever else the encoding carries. -/
def dom : Set (List ℕ) :=
  {x | ∃ (m : ℕ) (ps rest : List ℕ), x = ps.length :: m :: (ps ++ rest)}

/-- Words of that shape that fit into `w`-bit words, in the submission's standard sense:
every entry `v` satisfies `151 · (|x| + v + 1) ≤ 2 ^ w`. -/
def admissibleDom (w : ℕ) : Set (List ℕ) :=
  {x | x ∈ dom ∧ Lax470956.ParameterizedComplexity.Fits 151 w x}

/-- Every element is at most the largest. -/
theorem le_foldr_max : ∀ {l : List ℕ} {v : ℕ}, v ∈ l → v ≤ l.foldr max 0
  | a :: t, v, hv => by
      rcases List.mem_cons.mp hv with rfl | hv'
      · simp
      · have := le_foldr_max hv'
        simp only [List.foldr_cons, le_max_iff]
        exact Or.inr this

/-- The largest entry of a list is one of them, unless the list has none above zero. -/
theorem foldr_max_mem_or_zero : ∀ l : List ℕ, l.foldr max 0 ∈ l ∨ l.foldr max 0 = 0
  | [] => Or.inr rfl
  | a :: t => by
      simp only [List.foldr_cons]
      rcases le_total a (t.foldr max 0) with hle | hle
      · rw [max_eq_right hle]
        rcases foldr_max_mem_or_zero t with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
      · rw [max_eq_left hle]
        exact Or.inl List.mem_cons_self

/-- A sublist's largest entry is at most the whole list's. -/
theorem foldr_max_le_of_mem {l l' : List ℕ} (h : ∀ v ∈ l, v ≤ l'.foldr max 0) :
    l.foldr max 0 ≤ l'.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldr_cons, max_le_iff]
      exact ⟨h a List.mem_cons_self, ih fun v hv => h v (List.mem_cons_of_mem _ hv)⟩

/-- The `j`-th processing time of a word of this shape. -/
theorem proc_eq {m : ℕ} {ps rest : List ℕ} (j : ℕ) :
    Lax470956.InstanceEncoding.proc (ps.length :: m :: (ps ++ rest)) j
      = (ps ++ rest).getD j 0 := by
  show (ps.length :: m :: (ps ++ rest)).getD (2 + j) 0 = _
  rw [show 2 + j = j + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]

/-- Reading the processing-time block back off its own positions returns it. -/
theorem map_proc_range {m : ℕ} {ps rest : List ℕ} :
    (List.range ps.length).map
        (Lax470956.InstanceEncoding.proc (ps.length :: m :: (ps ++ rest))) = ps := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  rw [List.getElem_map, List.getElem_range, proc_eq, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h₂, List.getElem?_eq_getElem h₂, Option.getD_some]

/-- On a word of this shape, the largest processing time is the fold the concept
defines. -/
theorem pmaxOf_eq {m : ℕ} {ps rest : List ℕ} :
    Lax470956.SchedulingProblems.pmaxOf (ps.length :: m :: (ps ++ rest))
      = ps.foldr max 0 := by
  have hjc : Lax470956.InstanceEncoding.jobCount (ps.length :: m :: (ps ++ rest))
      = ps.length := rfl
  rw [Lax470956.SchedulingProblems.pmaxOf, hjc, map_proc_range]

theorem com_ok : Com.Ok layout com := by
  simp [com, body, cond, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by simp [Layout.const]

/-! ### The Loop -/

/-- The invariant: the counter has the processing times still to be read left to go,
the largest read so far together with those still to come is the largest overall, and
nothing has been written. -/
def Inv (B : ℕ) (σ₀ : Env) (goal : ℕ) (rest : List ℕ) (τ : Env) : Prop :=
  ∃ ps' : List ℕ, τ.inp = ps' ++ rest ∧
    τ.vars "n" = τ.vars "i" + ps'.length ∧
    τ.vars "n" < B ∧ τ.vars "best" < B ∧ (∀ v ∈ ps', v < B) ∧
    max (τ.vars "best") (ps'.foldr max 0) = goal ∧ τ.out = σ₀.out

/-- The loop reads the whole processing-time block, leaving the largest entry in
`best`, at a cost of at most `15` per entry plus `4`. -/
theorem loop_run {B goal : ℕ} {rest : List ℕ} (σ₀ τ₀ : Env)
    (hI : Inv B σ₀ goal rest τ₀) :
    ∃ σ', Run B (.while cond body) τ₀ σ'
        (15 * (τ₀.vars "n" - τ₀.vars "i") + 4) ∧
      σ'.vars "best" = goal ∧ σ'.out = σ₀.out := by
  have hstep : ∀ τ : Env, Inv B σ₀ goal rest τ → cond.evalB B τ = some true →
      ∃ τ', Run B body τ τ' 11 ∧ Inv B σ₀ goal rest τ' ∧
        (τ'.vars "n" - τ'.vars "i") < (τ.vars "n" - τ.vars "i") := by
    rintro τ ⟨ps', hinp, hn, hnB, hbB, hpsB, hmax, hout⟩ hcond
    have hlt : τ.vars "i" < τ.vars "n" := by simp [cond] at hcond; omega
    obtain ⟨v, ps'', hps⟩ : ∃ v ps'', ps' = v :: ps'' := by
      rcases h : ps' with _ | ⟨v, ps''⟩
      · rw [h] at hn; simp at hn; omega
      · exact ⟨v, ps'', rfl⟩
    subst hps
    have hvB : v < B := hpsB v (by simp)
    have htape : τ.inp = v :: (ps'' ++ rest) := by rw [hinp]; simp
    have hps''B : ∀ u ∈ ps'', u < B := fun u hu => hpsB u (by simp [hu])
    have hnB' : τ.vars "i" + 1 < B := by omega
    by_cases hbv : τ.vars "best" < v
    · refine ⟨_, Run.seq (Run.read htape)
        (Run.seq (Run.ite_true (b := .lt (.var "best") (.var "v"))
            (by simp; omega) (Run.assign (x := "best") (v := v) (by simp; omega)))
          (Run.assign (x := "i") (v := τ.vars "i" + 1) (by simp; omega))),
        ⟨ps'', by simp, by simp at hn ⊢; omega, by simpa using hnB, by simpa using hvB,
          hps''B, ?_, by simpa using hout⟩, by simp; omega⟩
      simp [Env.setVar]
      rw [← hmax, List.foldr_cons]
      omega
    · refine ⟨_, (Run.seq (Run.read htape)
        (Run.seq (Run.ite_false (b := .lt (.var "best") (.var "v"))
            (by simp; omega) Run.skip)
          (Run.assign (x := "i") (v := τ.vars "i" + 1) (by simp; omega)))).mono (by simp),
        ⟨ps'', by simp, by simp at hn ⊢; omega, by simpa using hnB, by simpa using hbB,
          hps''B, ?_, by simpa using hout⟩, by simp; omega⟩
      simp [Env.setVar]
      rw [← hmax, List.foldr_cons]
      omega
  obtain ⟨σ', hrun, ⟨ps', hinp, hn, _, _, _, hmax, hout⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := cond) (c := body) (Inv B σ₀ goal rest)
      (fun τ => τ.vars "n" - τ.vars "i") 11
      (fun τ hτ => by
        obtain ⟨_, _, hn, hnB, _, _, _, _⟩ := hτ
        exact ⟨decide (τ.vars "i" < τ.vars "n"), by simp [cond]; omega⟩)
      hstep hI
  have hexit : ¬ σ'.vars "i" < σ'.vars "n" := by simp [cond] at hfalse; omega
  have hnil : ps' = [] := by
    rcases h : ps' with _ | ⟨u, l⟩
    · rfl
    · rw [h] at hn; simp at hn; omega
  subst hnil
  refine ⟨σ', hrun.mono (by simp [cond]), ?_, hout⟩
  simpa using hmax

/-! ### The Whole Program -/

theorem solves : Solves layout com dom
    (fun x => [Lax470956.SchedulingProblems.pmaxOf x])
    (fun x => x.length + x.foldr max 0 + 2) (fun x => 15 * x.length + 12) where
  ok := com_ok
  inp := by
    rintro x ⟨m, ps, rest, rfl⟩ v hv
    have := le_foldr_max hv
    omega
  run := by
    rintro x ⟨m, ps, rest, rfl⟩
    set L := (ps.length :: m :: (ps ++ rest)) with hL
    set B := L.length + L.foldr max 0 + 2 with hB
    have hsum : L.length = 2 + ps.length + rest.length := by simp [hL]; omega
    have hpsB : ∀ v ∈ ps, v < B := fun v hv => by
      have : v ≤ L.foldr max 0 := le_foldr_max (by simp [hL, hv])
      omega
    have hmaxle : ps.foldr max 0 ≤ L.foldr max 0 :=
      foldr_max_le_of_mem fun v hv => le_foldr_max (by simp [hL, hv])
    set σ₀ : Env := initEnv (fun _ => 0) L with hσ₀
    obtain ⟨σ', hloop, hbest, hout⟩ :=
      loop_run (B := B) (goal := ps.foldr max 0) (rest := rest) σ₀
        (({ ({ σ₀.setVar "n" ps.length with inp := m :: (ps ++ rest) }).setVar "m" m with
            inp := ps ++ rest }.setVar "i" 0).setVar "best" 0)
        ⟨ps, by simp, by simp, by simp [hB, hsum]; omega, by simp [hB],
          hpsB, by simp, by simp [hσ₀, initEnv]⟩
    refine ⟨fun _ => 0, _,
      (Run.seq (Run.read (by simp [hσ₀, initEnv, hL]))
        (Run.seq (Run.read (by simp))
          (Run.seq (Run.assign (x := "i") (v := 0) (by simp [hB]))
            (Run.seq (Run.assign (x := "best") (v := 0) (by simp [hB]))
              (Run.seq hloop
                (Run.write (v := σ'.vars "best") (by
                  rw [hbest]; simp [hB]; omega))))))).mono ?_, ?_⟩
    · simp [hL]; omega
    · show σ'.out ++ [σ'.vars "best"] = _
      rw [hout, hbest, hσ₀]
      simp [initEnv, hL, pmaxOf_eq]

/-- **The largest processing time, end to end.** The compiled program writes
`pmaxOf x` within `10 · (15 |x| + 12) + 1` instructions, at every word length at which
the values and the layout fit. -/
theorem prog_computesInTime (w : ℕ) :
    ComputesInTime w prog (admissibleDom w)
      (fun x => [Lax470956.SchedulingProblems.pmaxOf x])
      (fun x => 151 * (x.length + 1)) := by
  have hsolves : Solves layout com (admissibleDom w)
      (fun x => [Lax470956.SchedulingProblems.pmaxOf x])
      (fun x => x.length + x.foldr max 0 + 2) (fun x => 15 * x.length + 12) :=
    ⟨solves.ok, fun x hx => solves.inp x hx.1, fun x hx => solves.run x hx.1⟩
  refine computesInTime_of_solves hsolves (fun x hx => ?_)
    (fun x _ => by rw [const_eq]; omega)
  obtain ⟨⟨m, ps, rest, rfl⟩, hfits⟩ := hx
  set L := (ps.length :: m :: (ps ++ rest)) with hL
  have hlen : 2 ≤ L.length := by simp [hL]
  have hhead : ps.length ∈ L := by simp [hL]
  have hbig : 151 * (L.length + L.foldr max 0 + 1) ≤ 2 ^ w := by
    rcases foldr_max_mem_or_zero L with hm | hm
    · exact hfits _ hm
    · rw [hm]
      have := hfits _ hhead
      omega
  refine fitsWords_of_max_le (by omega) ?_
  simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
  omega

/-! ### The Domain of the Concept Statement -/

/-- A word encoding a decision instance has the shape the program expects: the job
count, the machine count, then that many processing times, then the rest. -/
theorem decisionInstances_subset_dom :
    Lax470956.InstanceEncoding.DecisionInstances ⊆ dom := by
  rintro x ⟨I, W, y, rfl, henc⟩
  have hy := henc.length_eq
  have hjc := henc.jobCount_eq
  obtain ⟨a, t, rfl⟩ : ∃ a t, y = a :: t := by
    rcases y with _ | ⟨a, t⟩
    · simp at hy; omega
    · exact ⟨a, t, rfl⟩
  obtain ⟨b, u, rfl⟩ : ∃ b u, t = b :: u := by
    rcases t with _ | ⟨b, u⟩
    · simp at hy; omega
    · exact ⟨b, u, rfl⟩
  have ha : a = I.jobs := hjc
  subst ha
  have hu : I.jobs ≤ (u ++ [W]).length := by simp at hy ⊢; omega
  refine ⟨b, (u ++ [W]).take I.jobs, (u ++ [W]).drop I.jobs, ?_⟩
  rw [List.length_take, Nat.min_eq_left hu, List.take_append_drop]
  simp

/--
---
conclusion: Lax470956.SchedulingProblems.pmaxOf_computesInTime
---
The program reads the two header entries, then the `n` processing times, keeping the
largest seen, and writes it. The loop costs `15` per entry and the whole command `12`
more, and the compiler charges `10` machine instructions per unit of that cost plus a
final `halt`, so `151 · (|x| + 1)` covers it.

The domain is the submission's standard fitting condition rather than a bound on the
sum of the word: the value bound the IMP+ program needs is the length of the word plus
its largest entry, which one entry's fitting condition already supplies.
-/
theorem pmaxOf_computesInTime :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ Lax470956.InstanceEncoding.DecisionInstances ∧
          Lax470956.ParameterizedComplexity.Fits c w x}
        (fun x => [Lax470956.SchedulingProblems.pmaxOf x])
        (fun x => c * (x.length + 1)) :=
  ⟨prog, 151, fun w x hx =>
    prog_computesInTime w x ⟨decisionInstances_subset_dom hx.1, hx.2⟩⟩

end Lax470956Proofs.Pmax
