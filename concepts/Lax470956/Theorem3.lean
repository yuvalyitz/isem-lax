import Lax470956.SchedulingProblems

/-!
---
title: Interval Scheduling Is Fixed-Parameter Tractable for the Machines and the Largest Processing Time
type: theorem
---
Interval scheduling with eligible machine sets is fixed-parameter tractable for the
combined parameter $m + p_{\max}$. There are one word RAM program and one constant $c$
such that, at every word length admitting the input and the configuration table,
the program halts within
$$c \cdot (m \cdot p_{\max} + 1)^{2m} \cdot (m+1) \cdot (|x|+1)$$
instructions and writes $1$ if a feasible schedule of weight at least $W$ exists and $0$ if none
does.

The algorithm sweeps the time axis. At each point it records, for every machine, how much
longer that machine stays busy (a vector of $m$ numbers, each at most $p_{\max}$) and the
best weight achieving that configuration. A preprocessing step first discards all but a
bounded number of jobs per starting time, so the number of jobs alive at any moment, and
hence the number of reachable configurations, is bounded by a function of the parameter alone.

Together with the first theorem, which rules out fixed-parameter tractability for $m$
alone unless $\mathrm{W}[1] = \mathrm{FPT}$, and the second, which rules it out for
$p_{\max}$ alone unless $\mathrm{P} = \mathrm{NP}$, this locates the problem: the
combined parameter is tractable and neither half of it is.

# Formalization Notes

Two statements are made. The first gives the running time explicitly, with the dependence on
the parameter written out, for the words that leave room for the algorithm's table. The second
is `FPT` from `ParameterizedComplexity`, for every word whose entries fit.

The first statement's domain has a second clause beyond `Fits`. `Fits` says that the entries
of the instance are words, which is needed because deadlines and weights are not bounded by the
length of the word. The second clause says that $c\,(m\,p_{\max}+1)^{2m}$ is a word. The
algorithm's table is indexed by machine configurations, there are $(p_{\max}+1)^m$ of them, and
a machine with $2^w$ cells cannot address a larger table, so without the clause the claimed
time would not be achievable.

`FPT` has no such clause, so the second statement is not a weakening of the first. The
program compares the word's length with the table: when the word is at least as long as the
table, the table fits, since every admissible word fits with room for a multiple of its
length; when the word is shorter than the table, its length is bounded by a function of the
parameter, and the program tries every schedule instead. The function of the parameter is
then much larger than $(m\,p_{\max})^{2m}$.

The program and the constant are quantified before the word length, so one program serves
every word length that admits its input. A program chosen after the word length could hide an
unbounded amount of information in its literals and would be a family of programs, not an
algorithm.

The theorem is stated for the decision problem with a threshold rather than for the
optimization problem. The algorithm computes the optimum and the comparison is one further
instruction; the decision version has the same shape as the two hardness theorems.
-/

namespace Lax470956.Theorem3

open Lax808846.Ram Lax808846.RamComputes
open Lax470956.InstanceEncoding Lax470956.SchedulingProblems Lax470956.ParameterizedComplexity

open Classical in
/-- **Theorem 3.** One word RAM program decides interval scheduling with eligible machine
sets within `c * (m * p_max + 1) ^ (2 * m) * (m + 1) * (|x| + 1)` instructions, at every
word length admitting the instance and a table indexed by machine configurations.

The paper states the bound as `O((m · p_max)^{2m} · m · n)`. Written with an explicit
constant, the product needs the `+1`s: with no machines, or with no jobs, `(m · p_max)^{2m} · m`
is zero, and no program answers in zero instructions. Apart from those terms, the bound differs
from the paper's in measuring the input by `|x|` instead of `n`. -/
axiom fptTime_byMachinesAndPmax :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧
          c * (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) ≤ 2 ^ w}
        (fun x => if byMachinesAndPmax.Yes x then [1] else [0])
        (fun x => c * (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) *
          (machineCount x + 1) * (x.length + 1))

/-- **Theorem 3**, in the general form: the problem parameterized by `m + p_max` is
fixed-parameter tractable.

It does not follow from the explicit bound by weakening the function of the parameter,
because `FPT` asks for an answer on every word whose entries fit, and there the table need not
be addressable. Where it is not, the proof tries every schedule, and the function of the
parameter is much larger than `(m · p_max)^{2m}`. -/
axiom fpt_byMachinesAndPmax : FPT byMachinesAndPmax

end Lax470956.Theorem3
