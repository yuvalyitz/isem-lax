import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold

/-!
---
title: Interval Scheduling with Eligible Machine Sets
type: definition
---
An instance consists of $n$ jobs and $m$ identical parallel machines. Job $j$ has
a processing time $p_j \ge 1$, a deadline $d_j \ge p_j$, a weight $w_j$, and a set
$M_j$ of *eligible* machines. Each job is an interval: job $j$, if scheduled, occupies
exactly $[d_j - p_j,\, d_j)$, so a schedule chooses only *which* machine runs a job,
never when.

A schedule assigns to every job either an eligible machine or nothing. It is *feasible*
if no machine is assigned two jobs whose intervals overlap. Its weight is the total
weight of the jobs it schedules. The optimization problem asks for a feasible schedule
of maximum weight; the decision problem asks whether weight $W$ is attainable.

# Formalization Notes

Jobs and machines are `Fin n` and `Fin m` rather than abstract finite types. The
difference matters: an instance is something a machine is handed as a word, and a word
presents its jobs in an order. An abstract finite type would have to be equipped with an
enumeration before anything could be encoded, and the enumeration — not the type — is
what the encoding would then describe.

The two standing conventions $p_j \ge 1$ and $p_j \le d_j$ are fields of the structure,
as they are hypotheses of every statement in the source. Without the first, a job of
processing time zero occupies an empty interval and overlaps nothing; without the second,
the truncated subtraction $d_j - p_j$ would clamp to zero.

Overlap is defined on the half-open intervals, so jobs meeting end-to-start do not
overlap. `Feasible` constrains only the pairs a schedule actually places on a common
machine, and says nothing about rejected jobs; `Complete` is the separate condition that
no job is rejected, which the second theorem of this submission is about.

The weight of a schedule sums over all jobs, contributing zero for a rejected one, rather
than summing over the scheduled ones. The two agree, and the first needs no decidability
of the set of scheduled jobs.
-/

namespace Lax888481.Scheduling

/-- An instance of interval scheduling with eligible machine sets: `jobs` jobs on
`machines` machines, each job with a processing time, a deadline, a weight, and the set
of machines allowed to run it. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of machines. -/
  machines : ℕ
  /-- The processing time `p j` of job `j`. -/
  p : Fin jobs → ℕ
  /-- The deadline `d j` of job `j`. -/
  d : Fin jobs → ℕ
  /-- The weight `w j` of job `j`. -/
  w : Fin jobs → ℕ
  /-- The machines eligible to run job `j`. -/
  eligible : Fin jobs → Finset (Fin machines)
  /-- Every job takes at least one time unit. -/
  p_pos : ∀ j, 0 < p j
  /-- Every job fits before its deadline. -/
  p_le_d : ∀ j, p j ≤ d j

namespace Instance

variable (I : Instance)

/-- The time at which job `j` starts, namely `d j - p j`: a job occupies exactly the
interval `[d j - p j, d j)`. -/
def start (j : Fin I.jobs) : ℕ := I.d j - I.p j

/-- Jobs `j` and `j'` *overlap*: their half-open intervals meet. -/
def Overlap (j j' : Fin I.jobs) : Prop :=
  I.start j < I.d j' ∧ I.start j' < I.d j

/-- A schedule assigns each job an eligible machine, or nothing. -/
abbrev Schedule := Fin I.jobs → Option (Fin I.machines)

variable {I}

/-- A schedule is *feasible* if it places every scheduled job on an eligible machine and
never places two overlapping jobs on the same machine. -/
def Feasible (σ : I.Schedule) : Prop :=
  (∀ j i, σ j = some i → i ∈ I.eligible j) ∧
  (∀ j j' i, j ≠ j' → I.Overlap j j' → σ j = some i → σ j' ≠ some i)

/-- A schedule is *complete* if it rejects no job. -/
def Complete (σ : I.Schedule) : Prop := ∀ j, σ j ≠ none

/-- The weight of a schedule: the total weight of the jobs it schedules. -/
def weight (σ : I.Schedule) : ℕ := ∑ j, (σ j).elim 0 fun _ => I.w j

variable (I)

/-- `I` admits a feasible schedule of weight at least `W`. -/
def HasWeight (W : ℕ) : Prop := ∃ σ : I.Schedule, Feasible σ ∧ W ≤ weight σ

/-- `I` admits a feasible schedule that rejects no job. -/
def AllSchedulable : Prop := ∃ σ : I.Schedule, Feasible σ ∧ Complete σ

/-- The largest processing time in `I`, and `0` if there are no jobs. -/
def pmax : ℕ := Finset.univ.sup I.p

end Instance

end Lax888481.Scheduling
