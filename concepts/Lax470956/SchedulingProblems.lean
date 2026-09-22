import Lax470956.InstanceEncoding
import Lax470956.ParameterizedComplexity

/-!
---
title: The scheduling problems, parameterized
type: definition
---
Interval scheduling with eligible machine sets, as parameterized problems on words:
the decision problem "is weight $W$ attainable?" parameterized by the number $m$ of
machines, the same problem parameterized by $m + p_{\max}$, and the problem "can every
job be scheduled?" parameterized by $p_{\max}$.

The three theorems of this submission are about these three problems: the first is
W[1]-hard, the second is fixed-parameter tractable, and the third is NP-hard already
when its parameter is bounded by an absolute constant.

# Formalization notes

Each parameter is read off the word rather than supplied beside it. The number of
machines is the word's second entry, so it costs a program nothing to obtain; $p_{\max}$
is the largest processing time, which a program computes in one pass over the
processing-time block, and which the parameter function therefore also computes rather
than reads. Both are functions of the word alone, as the definition of a parameterized problem asks.

A word outside the domain has no meaningful parameter. The parameter function is total
regardless — it returns the second entry, or the largest entry of a block that may not
exist — and nothing is claimed about its value there, since every statement quantifies
over admissible words only.

`pmaxOf` is defined on the word rather than on the decoded instance so that the
parameter of a problem is manifestly a function of the input. On an admissible word the
two agree, which is a lemma of the proof layer rather than part of the definition.
-/

namespace Lax470956.SchedulingProblems

open Lax470956.Scheduling Lax470956.InstanceEncoding Lax470956.ParameterizedComplexity
open Lax808846.Ram Lax808846.RamComputes

/-- The largest processing time declared by a word: the largest of the `n` entries of
its processing-time block. -/
def pmaxOf (x : List ℕ) : ℕ :=
  ((List.range (jobCount x)).map (proc x)).foldr max 0

/-- **Interval scheduling with eligible machine sets**, parameterized by the number of
machines. -/
def byMachines : Problem where
  Domain := DecisionInstances
  Yes x := ∃ I W, EncodesDecisionInstance x I W ∧ I.HasWeight W
  param x := machineCount x

/-- The same problem, parameterized by the number of machines together with the largest
processing time. -/
def byMachinesAndPmax : Problem where
  Domain := DecisionInstances
  Yes x := ∃ I W, EncodesDecisionInstance x I W ∧ I.HasWeight W
  param x := machineCount x + pmaxOf x

/-- **Scheduling every job**: is there a feasible schedule that rejects no job?
Parameterized by the largest processing time. Instances carry no threshold. -/
def allSchedulableByPmax : Problem where
  Domain := Instances
  Yes x := ∃ I, EncodesInstance x I ∧ I.AllSchedulable
  param x := pmaxOf x

/-- **The parameter is computed by a word RAM program in linear time.** One program and
one constant `c` such that, at every word length, on every decision instance whose
entries fit, the program halts within `c · (|x| + 1)` instructions having written the
largest processing time.

A parameterized problem whose parameter no machine can read is not one a machine can be
handed, and the parameter of the second and third problems above is not an entry of the
word but a maximum over a block of it. This says that reading it costs a single pass,
so that nothing in the running time of the third theorem is hidden in obtaining the
parameter it is stated in terms of. -/
axiom pmaxOf_computesInTime :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x}
        (fun x => [pmaxOf x])
        (fun x => c * (x.length + 1))

end Lax470956.SchedulingProblems
