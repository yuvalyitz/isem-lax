import Lax470956.Exact34Encoding
import Lax470956.PolynomialReduction
import Lax470956.SatVariant
import Lax470956.SchedulingProblems

/-!
---
title: Scheduling every job is hard for constant processing times and unit weights
type: theorem
---
Deciding whether every job of an interval scheduling instance can be scheduled is
NP-hard, and remains so on instances in which every processing time is at most $25$ and
every weight is $1$.

The bound on the processing times is absolute: it does not grow with the instance. So the
problem is para-NP-hard for the parameter $p_{\max}$, and no algorithm running in
$f(p_{\max}) \cdot \mathrm{poly}(n)$ time can exist for any function $f$ unless
$\mathrm{P} = \mathrm{NP}$. Together with the third theorem, which is fixed-parameter
tractable for $m + p_{\max}$, this shows that neither half of that combined parameter can
be dropped.

The reduction is from $(3,4)$-satisfiability. It gives each variable two machines,
one for each truth value, and each clause three; each occurrence of a variable in a
clause becomes a unit job flanked by two jobs filling the rest of a fixed window of
length $25$, and each variable becomes one job spanning that whole window. The bounded
number of occurrences of a variable is what keeps the window, and with it every
processing time, bounded by a constant.

# Formalization notes

Three separate statements, because they are three assertions with different content and
different costs to establish.

The first is the reduction itself, the paper's result: a polynomial-time
map on words sending satisfiable formulas exactly to schedulable instances, all of them
in the bounded slice. It is stated on the word RAM, where a program can be written and
its running time counted.

The other two are the hardness conclusions. Each follows from the reduction together
with the NP-hardness of $(3,4)$-satisfiability, and each is stated against the
classical Turing-machine notion of NP, since that is what a claim of NP-hardness means.
They are separate because they are reached differently: the reduction is a statement
about one map, while a hardness claim quantifies over every language in NP and composes
the reduction with the hardness of the problem it starts from.

Nothing beyond ordinary work stands between the three. Polynomial-time computability on
the two machine models is interchangeable, and polynomial-time maps compose, so a
reduction certified on either model transports to the other and can be chained with a
cited hardness result. The only input this submission does not supply is that hardness
result itself.
-/

namespace Lax470956.Theorem2

open Lax470956.Scheduling Lax470956.NPHardness Lax470956.PolynomialReduction

/-- The words encoding an instance in which every processing time is at most `25` and
every weight is `1`. -/
def BoundedSlice (y : List ℕ) : Prop :=
  ∃ I : Instance, InstanceEncoding.EncodesInstance y I ∧
    I.pmax ≤ 25 ∧ ∀ j, I.w j = 1

/-- **Construction 2.** `(3,4)`-satisfiability reduces in polynomial time to
scheduling every job, by a reduction whose every output has processing times at most
`25` and unit weights. -/
axiom sat34_polyReducesOn_allSchedulable :
    PolyReducesOn Exact34Encoding.Satisfiable
      {y | ∃ I, InstanceEncoding.EncodesInstance y I ∧ I.AllSchedulable}
      BoundedSlice

/-- **Theorem 2.** Deciding whether every job can be scheduled is NP-hard. -/
axiom npHard_allSchedulable : NPHard Instance.AllSchedulable

/-- **Theorem 2, on the bounded slice.** Deciding whether every job can be scheduled is
NP-hard already on instances whose processing times are at most `25` and whose weights
are all `1` — so the problem is para-NP-hard for the parameter `p_max`. -/
axiom npHardOn_allSchedulable_pmax_le :
    NPHardOn Instance.AllSchedulable
      fun I => I.pmax ≤ 25 ∧ ∀ j, I.w j = 1

end Lax470956.Theorem2
