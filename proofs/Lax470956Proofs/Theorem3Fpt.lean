import Lax470956Proofs.FptMain
import Lax470956.Theorem3

/-!
Theorem 3, stated as fixed-parameter tractability: one program that decides on every word.
-/

namespace Lax470956Proofs.Theorem3Fpt

open Lax470956.InstanceEncoding Lax470956.SchedulingProblems
open Lax470956.ParameterizedComplexity

/--
---
conclusion: Lax470956.Theorem3.fpt_byMachinesAndPmax
---
The explicit bound of the first form is stated for the words that leave room for the table.
Fixed-parameter tractability is stated for every word whose entries fit, and there the table
may not be addressable: a machine with `2 ^ w` cells cannot hold `(p_max + 1) ^ m` entries when
that exceeds `2 ^ w`, although every entry of the word is a word.

The program first computes `min ((p_max + 1) ^ m) (|x| + 1)` by repeated multiplication, testing
each step by a division so that no intermediate value exceeds `|x| + 1`, and compares it with
`|x|`.

If the table has at most `|x|` entries, the sweep of the first form runs unchanged, within
`1000 · (p_max+1)^m · (m+1) · (|x|+1)` instructions.

Otherwise `|x| < (p_max + 1) ^ m ≤ (k + 1) ^ k`, where `k = m + p_max` is the parameter, so the
word, and with it the number of jobs `n`, is bounded by a function of the parameter alone. The
program then tries every schedule. An odometer of `n` digits in base `m + 1` runs through them,
each digit naming a machine or rejecting the job. Each string is checked against the word:
every job on an eligible machine, no two overlapping jobs on one machine, and the weight added
up with a cap at the threshold. There are `(m + 1) ^ n` strings, each tested in time polynomial
in the length, and `n ≤ |x|`.

The function of the parameter is `g k = 4000 · (k+1) · (k+1)^k · (k+1)^((k+1)^k)`, much larger
than the `(m · p_max)^{2m}` of the first form, which is the cost where the table fits.
-/
theorem fpt_byMachinesAndPmax : FPT byMachinesAndPmax :=
  Lax470956Proofs.FptMain.fpt

end Lax470956Proofs.Theorem3Fpt
