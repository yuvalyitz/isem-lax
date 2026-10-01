import Lax470956.Scheduling
import Mathlib.Algebra.Order.Monoid.WithTop

/-!
---
title: The Dynamic Program for Interval Scheduling, and Its State Space
type: definition
---
The algorithm behind the third theorem. It sweeps the time axis, carrying at each
instant a *state* — which job, if any, occupies each machine — and the best total weight
of the jobs started so far that is consistent with that state. A state at time $t+1$ may
follow a state at time $t$ when every job still running continues on its own machine and
every job appearing at $t+1$ that had already started was already there.

Writing $\mathrm{opt}_t(s)$ for the best weight of jobs started by time $t$ over the
feasible schedules whose occupancy at $t$ is exactly $s$, the recursion is
$$\mathrm{dp}_{t+1}(s') = \max_{s \to s'} \mathrm{dp}_t(s) + \mathrm{fresh}_{t+1}(s'),$$
with $\mathrm{dp}_0(s)$ the weight of the jobs $s$ starts. At the horizon every machine
is idle and the value is the optimum of the instance.

The number of states at any instant is at most $(a_t+1)^m$, where $a_t$ is the number of
jobs alive then: a state chooses, for each of the $m$ machines, one job alive at $t$ or
nothing. This is where fixed-parameter tractability comes from — the table is indexed by
the parameter, not by the instance — and it is why the preprocessing step, which bounds
$a_t$ by a function of $m$ and $p_{\max}$ alone, completes the argument.

# Formalization Notes

A state is a total function from machines to `Option` jobs, so a machine is idle exactly
when it is mapped to `none`. Defining it as a partial injection would be closer to the
intent and further from what a table is indexed by; the injectivity that an occupancy
has is a clause of `ValidState` instead.

The value of the table is `WithBot ℕ` rather than `ℕ`, with `⊥` for a state no feasible
schedule realizes. The distinction is needed: a state of weight zero and a state that
cannot occur are different, and a maximum over an empty set of schedules has to be
smaller than every real value rather than equal to zero.

`dp` is a recursion on the time index and is computable, while `optAt` quantifies over
schedules and is not. They are separate definitions so that their agreement is a theorem.
That theorem is the paper's Lemma 6, and it justifies running the recursion in place of the
specification.

The state-space bound is stated as a cardinality of a `Finset` of states rather than as
an asymptotic count. It is an exact inequality, as a running-time argument needs.
-/

namespace Lax470956.DynamicProgram

open Lax470956.Scheduling Lax470956.Scheduling.Instance

variable (I : Instance)

/-- A snapshot of the machines at one instant: which job, if any, occupies each. -/
abbrev State : Type := Fin I.machines → Option (Fin I.jobs)

variable {I}

/-- Job `j` is running at time `t`, that is `t ∈ [d j - p j, d j)`. -/
def Active (t : ℕ) (j : Fin I.jobs) : Prop := I.start j ≤ t ∧ t < I.d j

instance (t : ℕ) (j : Fin I.jobs) : Decidable (Active t j) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (j j' : Fin I.jobs) : Decidable (I.Overlap j j') :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (σ : I.Schedule) : Decidable (Feasible σ) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (I)

/-- The value of an optimal schedule. -/
def optimum : ℕ := (Finset.univ.filter fun σ : I.Schedule => Feasible σ).sup weight

/-- The time horizon: every job has finished by then. -/
def horizon : ℕ := Finset.univ.sup I.d

/-- The total weight of the scheduled jobs that have started by time `t`. -/
def weightStarted (σ : I.Schedule) (t : ℕ) : ℕ :=
  ∑ j, if σ j ≠ none ∧ I.start j ≤ t then I.w j else 0

/-- The total weight of the jobs a state shows as *beginning* at time `t`. -/
def freshWeight (t : ℕ) (s : State I) : ℕ :=
  ∑ j, if (∃ i, s i = some j) ∧ I.start j = t then I.w j else 0

/-- A state that could be the machine occupancy at time `t`: every occupant is eligible
and active, and no job occupies two machines. -/
def ValidState (t : ℕ) (s : State I) : Prop :=
  (∀ i j, s i = some j → i ∈ I.eligible j ∧ Active t j) ∧
  (∀ i i' j, s i = some j → s i' = some j → i = i')

instance (t : ℕ) (s : State I) : Decidable (ValidState I t s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The transition relation: state `s` at time `t` may be followed by state `s'` at time
`t + 1`. A job still running continues on its machine, and a job appearing at `t + 1`
that had already started must have been there at `t`. -/
def Step (t : ℕ) (s s' : State I) : Prop :=
  ValidState I (t + 1) s' ∧
  (∀ i j, s i = some j → t + 1 < I.d j → s' i = some j) ∧
  (∀ i j, s' i = some j → I.start j ≤ t → s i = some j)

instance (t : ℕ) (s s' : State I) : Decidable (Step I t s s') :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {I}

/-- The machine occupancy at time `t` of the schedule `σ`. -/
noncomputable def runOf (σ : I.Schedule) (t : ℕ) : State I := fun i =>
  if h : ∃ j, σ j = some i ∧ Active t j then some h.choose else none

variable (I)

/-- The best total weight of jobs started by time `t`, over the feasible schedules whose
machine occupancy at time `t` is exactly `s`. `⊥` when there is no such schedule. -/
noncomputable def optAt (t : ℕ) (s : State I) : WithBot ℕ :=
  open Classical in
  (Finset.univ.filter fun σ : I.Schedule => Feasible σ ∧ runOf σ t = s).sup
    fun σ => (weightStarted I σ t : WithBot ℕ)

/-- **The dynamic program.** A recursion on the time index: the value of a state at
`t + 1` is the best value of a predecessor, plus the weight of the jobs beginning then. -/
def dp : ℕ → State I → WithBot ℕ
  | 0, s => if ValidState I 0 s then (freshWeight I 0 s : WithBot ℕ) else ⊥
  | t + 1, s' =>
      ((Finset.univ.filter fun s => Step I t s s').sup fun s => dp t s)
        + (freshWeight I (t + 1) s' : WithBot ℕ)

/-- The value the algorithm returns: the table at the horizon, with every machine idle. -/
def solve : WithBot ℕ := dp I (horizon I) fun _ => none

/-- The number of jobs alive at time `t`. -/
def aliveCount (t : ℕ) : ℕ := (Finset.univ.filter fun j => Active (I := I) t j).card

/-- **Lemma 6.** The recursion computes the specification: at every instant and every
state, the dynamic program's value is the best weight of jobs started by then over the
feasible schedules with that occupancy. -/
axiom dp_eq_optAt (I : Instance) (t : ℕ) (s : State I) : dp I t s = optAt I t s

/-- **Theorem 3, algorithmic half.** The dynamic program returns the optimum of the
instance. -/
axiom solve_eq_optimum (I : Instance) : solve I = (optimum I : WithBot ℕ)

/-- **The state-space bound.** At any instant there are at most `(a_t + 1) ^ m` valid
states, where `a_t` is the number of jobs alive then. -/
axiom card_validState_le (I : Instance) (t : ℕ) :
    (Finset.univ.filter fun s : State I => ValidState I t s).card
      ≤ (aliveCount I t + 1) ^ I.machines

end Lax470956.DynamicProgram
