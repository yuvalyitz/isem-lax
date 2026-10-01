import Lax470956.DynamicProgram

/-!
---
title: Preprocessing an Interval Scheduling Instance Down to a Bounded Number of Live Jobs
type: definition
---
The step that makes the dynamic program fixed-parameter tractable. Two jobs with the
same processing time and the same deadline occupy the same interval, so on any one
machine they are interchangeable; of the jobs sharing an interval and eligible on a
given machine, only the $m$ heaviest can ever be useful, because a schedule places at
most $m$ of them at once and a lighter one can always be exchanged for a heavier unused
one. Keeping, for each machine, the $m$ best jobs of each interval eligible there, and
discarding the rest, leaves the optimum unchanged.

What the step buys is a bound independent of the number of jobs. A job alive at time $t$
has a deadline in $(t, t+p_{\max}]$ and a processing time in $[1, p_{\max}]$, so there
are at most $p_{\max}^2$ intervals it could occupy; each interval keeps at most $m$ jobs
per machine and there are $m$ machines. So at most $p_{\max}^2 m^2$ surviving jobs are
alive at any one instant — a bound in the parameter alone. Fed into the state-space
bound of the dynamic program, this makes the table's size a function of $m$ and $p_{\max}$.

# Formalization Notes

Discarding is modelled as a set of kept jobs together with the best weight achievable
using only those, rather than as a second instance on a smaller job set. The two say the
same thing, and the first states it without transporting an instance along a change of
index type — which would make the statement about the transport as much as about the
preprocessing.

Ties in weight are broken by the job's index. "The $m$ best" has to be well defined, and
some tie-break is needed to define it; the index is the tie-break a program would use,
since it is the order the jobs arrive in. `Better` is the resulting strict linear order:
heavier, or equally heavy and earlier.

A job is kept when it is among the $m$ best *for some machine it is eligible on*, not
for all of them. The exchange argument needs this: a job is discarded only when every machine that could run
it already keeps $m$ better alternatives for its interval. It is also why the bound counts
machines twice.
-/

namespace Lax470956.Preprocessing

open Lax470956.Scheduling Lax470956.Scheduling.Instance Lax470956.DynamicProgram

variable (I : Instance)

/-- `j` is strictly better than `j'`: heavier, or equally heavy and earlier in index
order. -/
def Better (j j' : Fin I.jobs) : Prop :=
  I.w j' < I.w j ∨ (I.w j' = I.w j ∧ (j : ℕ) < (j' : ℕ))

instance (j j' : Fin I.jobs) : Decidable (Better I j j') :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The jobs occupying the interval `[dd - pp, dd)` that are eligible on machine `i`. -/
def slotOf (i : Fin I.machines) (dd pp : ℕ) : Finset (Fin I.jobs) :=
  Finset.univ.filter fun j => I.d j = dd ∧ I.p j = pp ∧ i ∈ I.eligible j

/-- The jobs occupying the same interval as `j` that are eligible on machine `i`. -/
def sameSlot (i : Fin I.machines) (j : Fin I.jobs) : Finset (Fin I.jobs) :=
  slotOf I i (I.d j) (I.p j)

/-- How many jobs of `j`'s slot on machine `i` beat `j`. -/
def rank (i : Fin I.machines) (j : Fin I.jobs) : ℕ :=
  ((sameSlot I i j).filter fun j' => Better I j' j).card

/-- **The preprocessing step.** Keep a job when, for some machine it is eligible on, it
is among the `m` best jobs of its interval there. -/
def keep : Finset (Fin I.jobs) :=
  Finset.univ.filter fun j => ∃ i ∈ I.eligible j, rank I i j < I.machines

/-- The best weight achievable by a feasible schedule that uses only jobs from `K`. -/
def optimumOn (K : Finset (Fin I.jobs)) : ℕ :=
  (Finset.univ.filter fun σ : I.Schedule => Feasible σ ∧ ∀ j, σ j ≠ none → j ∈ K).sup
    weight

/-- **Lemma 5.** Preprocessing does not change the optimum: the best weight achievable
using only the kept jobs is the optimum of the whole instance. -/
axiom optimumOn_keep (I : Instance) : optimumOn I (keep I) = optimum I

/-- **Observation 5.** At most `p_max ^ 2 * m ^ 2` kept jobs are alive at any one
instant — a bound in the parameter alone, with no dependence on the number of jobs. -/
axiom card_keep_alive_le (I : Instance) (t : ℕ) :
    ((keep I).filter fun j => Active t j).card ≤ I.pmax * I.pmax * (I.machines * I.machines)

end Lax470956.Preprocessing
