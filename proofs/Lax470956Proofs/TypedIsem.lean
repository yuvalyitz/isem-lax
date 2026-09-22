import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

namespace Lax470956Proofs.TypedIsem

/-!
# Interval Scheduling on Eligible Machines

The problem of Hermelin–Itzhaki–Molter–Shabtay, *"On the parameterized complexity of
interval scheduling with eligible machine sets"*, JCSS 144 (2024) 103533, Section 2.

An instance has `n` jobs and `m` machines. Job `j` carries a processing time `p j`, a
deadline `d j`, a weight `w j`, and a set `elig j` of machines permitted to run it, and
occupies exactly the interval `[d j - p j, d j)`. A schedule sends each job to a machine
or rejects it; it is feasible when every scheduled job sits on an eligible machine and no
two overlapping jobs share one. The objective is the total weight of scheduled jobs.

Jobs and machines are `Fintype`s rather than `Fin n` and `Fin m`, so that a construction
can name them structurally — as sums and subtypes of the objects they come from — instead
of through an ad-hoc enumeration.
-/

/-! ## 1. Interval Scheduling on Eligible Machines -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An instance of *Interval Scheduling on Eligible Machines* (Section 2).

Each job `j` has a processing time `p j`, a deadline `d j`, a weight `w j`, and a set
`elig j` of machines that may process it. Job `j` occupies exactly the interval
`[d j - p j, d j)`. `p_pos` and `p_le_d` are the paper's standing conventions. -/
structure ISEM where
  Job : Type
  Machine : Type
  jobFintype : Fintype Job
  jobDecEq : DecidableEq Job
  machineFintype : Fintype Machine
  machineDecEq : DecidableEq Machine
  p : Job → ℕ
  d : Job → ℕ
  w : Job → ℕ
  elig : Job → Finset Machine
  p_pos : ∀ j, 0 < p j
  p_le_d : ∀ j, p j ≤ d j

attribute [instance] ISEM.jobFintype ISEM.jobDecEq ISEM.machineFintype ISEM.machineDecEq

namespace ISEM

variable (I : ISEM)

/-- The number `n` of jobs. -/
def numJobs : ℕ := Fintype.card I.Job

/-- The number `m` of machines. -/
def numMachines : ℕ := Fintype.card I.Machine

/-- Start of job `j`'s interval `[d j - p j, d j)`. -/
def start (j : I.Job) : ℕ := I.d j - I.p j

/-- A schedule maps each job to a machine, or to `none` (`⊥` in the paper: rejected). -/
abbrev Schedule := I.Job → Option I.Machine

/-- Jobs `j` and `j'` conflict iff `[d j - p j, d j) ∩ [d j' - p j', d j') ≠ ∅`. -/
def Conflict (j j' : I.Job) : Prop :=
  I.start j < I.d j' ∧ I.start j' < I.d j

lemma conflict_symm {j j' : I.Job} (h : I.Conflict j j') : I.Conflict j' j := ⟨h.2, h.1⟩

/-- A schedule is feasible when every scheduled job sits on an eligible machine and
no two conflicting jobs share a machine. -/
def Feasible (σ : I.Schedule) : Prop :=
  (∀ j i, σ j = some i → i ∈ I.elig j) ∧
  (∀ j j' i, j ≠ j' → I.Conflict j j' → σ j = some i → σ j' ≠ some i)

/-- `w(σ) = ∑_{σ j ≠ ⊥} w j`, the objective of the problem. -/
def weight (σ : I.Schedule) : ℕ :=
  ∑ j : I.Job, (σ j).elim 0 (fun _ => I.w j)

/-- `I` admits a feasible schedule of total weight at least `W`. -/
def HasWeight (W : ℕ) : Prop :=
  ∃ σ : I.Schedule, I.Feasible σ ∧ W ≤ I.weight σ

/-- Two jobs whose intervals are separated do not conflict. -/
lemma not_conflict_of_le {j j' : I.Job} (h : I.d j ≤ I.start j') : ¬ I.Conflict j j' :=
  fun hc => absurd hc.2 (Nat.not_lt.mpr h)

lemma start_le_d (j : I.Job) : I.start j ≤ I.d j := Nat.sub_le _ _

/-- Five jobs whose intervals are laid out one after another are pairwise
non-conflicting. Used for the five jobs Lemma 1 puts on an edge selection machine. -/
lemma not_conflict_of_chain5 {j₁ j₂ j₃ j₄ j₅ : I.Job}
    (h₁ : I.d j₁ ≤ I.start j₂) (h₂ : I.d j₂ ≤ I.start j₃)
    (h₃ : I.d j₃ ≤ I.start j₄) (h₄ : I.d j₄ ≤ I.start j₅)
    {j j' : I.Job}
    (hj : j = j₁ ∨ j = j₂ ∨ j = j₃ ∨ j = j₄ ∨ j = j₅)
    (hj' : j' = j₁ ∨ j' = j₂ ∨ j' = j₃ ∨ j' = j₄ ∨ j' = j₅)
    (hne : j ≠ j') : ¬ I.Conflict j j' := by
  have s₁ := I.start_le_d j₁
  have s₂ := I.start_le_d j₂
  have s₃ := I.start_le_d j₃
  have s₄ := I.start_le_d j₄
  have s₅ := I.start_le_d j₅
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact I.not_conflict_of_le (by omega)
        | exact fun hc => I.not_conflict_of_le (by omega) (I.conflict_symm hc)

end ISEM

end Lax470956Proofs.TypedIsem
