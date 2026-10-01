import Lax888481.MulticolouredClique
import Lax888481.SchedulingProblems

/-!
---
title: Interval Scheduling Is W[1]-Hard for the Number of Machines
type: theorem
---
Multicoloured Clique, parameterized by the number of colours, fpt-reduces to interval
scheduling with eligible machine sets, parameterized by the number $m$ of machines.

Multicoloured Clique is W[1]-complete (Fellows, Hermelin, Rosamond and Vialette 2009), so
this says that interval scheduling with eligible machine sets is W[1]-hard for $m$. It is
therefore fixed-parameter tractable only if $\mathrm{W}[1] = \mathrm{FPT}$, which is not
believed: no algorithm solves it in $f(m) \cdot \mathrm{poly}(n)$ time unless the
hierarchy collapses. The third theorem of
this submission shows that adding $p_{\max}$ to the parameter does make the problem
tractable, so the two results together locate the boundary.

The reduction turns an instance with $k$ colours into a scheduling instance on
$\binom{k}{2}+1$ machines — one for each pair of colours, which selects an edge between
those two colour classes, and one validation machine. The parameter of the image depends
on the parameter of the source alone, so the reduction is an fpt-reduction
and not merely a correct one.

# Formalization Notes

The statement is the existence of an fpt-reduction, which unfolds to one map, one
program and one constant serving every instance and every admitting word length. It does
not mention the construction: which gadget realizes the reduction is the content of the
proof, not of the claim.

The claim carries the running time of the reduction, not only its combinatorial
correctness. The two are separate obligations and a proof has to discharge both; the
weights this reduction emits grow as a polynomial in the number of vertices and the
number of colours, so the fitting conditions on the image are not automatic and the
running-time half is where they are paid for.

The class W[1] is not formalized, so W[1]-hardness is not itself a statement of this
submission. What is stated is the reduction from the standard complete problem, which is
what a W[1]-hardness proof establishes. Reading it as W[1]-hardness uses two facts from
the literature and no Lean statement depends on them: that Multicoloured Clique is
W[1]-complete, and that fpt-reductions compose.
-/

namespace Lax888481.Theorem1

open Lax888481.ParameterizedComplexity

/-- **Theorem 1.** Multicoloured Clique fpt-reduces to interval scheduling with eligible
machine sets, parameterized by the number of machines. -/
axiom mcc_fptReduces_byMachines :
    MulticolouredClique.problem ≤fpt SchedulingProblems.byMachines

end Lax888481.Theorem1
