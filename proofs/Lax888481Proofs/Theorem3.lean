import Lax888481Proofs.SweepMain
import Lax888481.Theorem3

/-!
Theorem 3: the sweep, assembled into a word RAM program with its running time.
-/

namespace Lax888481Proofs.Theorem3

open Lax808846.Ram Lax808846.RamComputes
open Lax888481.InstanceEncoding Lax888481.SchedulingProblems
open Lax888481.ParameterizedComplexity
open scoped Classical

/--
---
conclusion: Lax888481.Theorem3.fptTime_byMachinesAndPmax
---
The program reads the word — whose own header says how long it is — and answers at once
when there is no machine or no job. Otherwise it runs eight passes. Four are
preprocessing: the largest processing time; the powers of `p_max + 1` that index the
table; a bucketing of the jobs by deadline into a linked list per deadline; and, for each
occupied deadline, whether it starts a block and which occupied deadline follows it
within `p_max`. The fifth walks the blocks and writes the jobs out in the order the sweep
wants them. This replaces a sort, which would cost `n log n`, more than a
function of the parameter times the length. The sixth is the sweep itself: a table
indexed by the machines' free durations, each capped at `p_max`, carried from one
deadline to the next. The last two read the best entry off the table and compare the
total with the threshold.

Three ingredients make the bound linear in the length. The order pass and the sweep are
amortized against a single potential — the jobs still to be written out — so the three
nested loops of the walk cost what they emit rather than what they scan. The blocks are
solved independently, which is sound because two occupied deadlines in different blocks
are at least `p_max` apart and so their jobs never overlap. And the eligibility scan is
charged to the total number of eligibility entries, which is one field of the word.

The constant is `12001`: it is what the fitting conditions have to supply for the
layout's thirteen arrays, and what the eight passes' costs add up to against
`(m · p_max + 1) ^ (2m) · (m+1) · (|x|+1)`.
-/
theorem fptTime_byMachinesAndPmax :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧
          c * (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) ≤ 2 ^ w}
        (fun x => if byMachinesAndPmax.Yes x then [1] else [0])
        (fun x => c * (machineCount x * pmaxOf x + 1) ^ (2 * machineCount x) *
          (machineCount x + 1) * (x.length + 1)) :=
  Lax888481Proofs.SweepMain.fptTime

end Lax888481Proofs.Theorem3
