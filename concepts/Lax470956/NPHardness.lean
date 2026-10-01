import Lax470956.BinaryEncoding
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: NP-Hardness of a Scheduling Problem, and on a Class of Instances
type: definition
---
A scheduling problem is *NP-hard* if every language in NP has a polynomial-time many-one
reduction to it, the reduction's output being an instance in the binary encoding.

It is *NP-hard on a class* $\mathcal C$ of instances if such a reduction exists whose
output always lies in $\mathcal C$. When $\mathcal C$ is a slice on which some parameter
is bounded by an absolute constant, this is *para-NP-hardness* for that parameter: it
rules out an algorithm running in $f(k)\cdot\mathrm{poly}(n)$ time for *every* function
$f$, unless $\mathrm{P} = \mathrm{NP}$ — a stronger and unconditional-in-$f$ conclusion
than W[1]-hardness, which rules out fixed-parameter tractability only under
$\mathrm{W}[1] \ne \mathrm{FPT}$.

# Formalization Notes

Hardness is defined by quantifying over NP, not against a fixed complete problem. NP is
available — `Lax434930` defines it — so the definition a textbook gives can be written
down, and there is no reason to substitute a reference problem for it as the
parameterized definition of this submission has to.

The reduction's target is an instance rather than a word, with the encoding applied by
the definition. This keeps a statement about a problem from also being a statement about
which words are well-formed, and it matches how graph problems are stated elsewhere in
the archive.

"NP-hard on a class" is one definition covering both a plain hardness claim, where the
class is everything, and a para-NP-hardness claim, where it is a bounded slice. Stating
the slice as a predicate on instances rather than as a bound on a parameter function
keeps it readable — "every emitted instance has $p_{\max} \le 25$ and unit weights" is
what the reduction actually guarantees, and what a reader checks it against.
-/

namespace Lax470956.NPHardness

open Lax470956.Scheduling Lax470956.BinaryEncoding
open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/-- A property of scheduling instances: a decision problem on them. -/
abbrev Problem := Instance → Prop

/-- `Q` is **NP-hard**: every language in NP reduces to it in polynomial time. -/
def NPHard (Q : Problem) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → Instance,
      Nonempty (Turing.TM2ComputableInPolyTime id encodeInstance f) ∧
      ∀ x, x ∈ A ↔ Q (f x)

/-- `Q` is **NP-hard on `C`**: every language in NP reduces to it in polynomial time by a
reduction all of whose outputs lie in `C`. -/
def NPHardOn (Q : Problem) (C : Instance → Prop) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → Instance,
      Nonempty (Turing.TM2ComputableInPolyTime id encodeInstance f) ∧
      ∀ x, C (f x) ∧ (x ∈ A ↔ Q (f x))

end Lax470956.NPHardness
