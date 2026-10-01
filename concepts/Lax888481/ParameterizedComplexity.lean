import Lax808846.RamComputes

/-!
---
title: Parameterized Problems and FPT-Reductions on a Word RAM
type: definition
---
A *parameterized problem* is a set of admissible input words, a yes-instance predicate on
them, and a parameter read off the word. It is *fixed-parameter tractable* if one word
RAM program decides it, on every admissible word $x$ of parameter $k$, within
$c\,g(k)\,(|x|+1)$ instructions for a constant $c$ and a function $g$ of the parameter
alone.

An *fpt-reduction* from $P$ to $Q$ is a map on words that sends admissible words to
admissible words, preserves and reflects yes-instances, raises the parameter by at most a
function of it, and is computed by one word RAM program within the same kind of bound.
Fpt-reductions compose, and $Q \in \mathrm{FPT}$ together with $P \le_{\mathrm{fpt}} Q$
gives $P \in \mathrm{FPT}$.

# Formalization Notes

The parameter is read off the input word, and the program is fixed before it: the
quantifier order puts the program and the constant before the instance, the parameter and
the word length. This is the uniformity of the definition. A definition that let the
program be chosen after $k$ would describe a family of programs, one per parameter, which
could hide unbounded advice in its literals.

`Fits` is the fitting condition, stated as an explicit inequality against `2 ^ w` rather
than through logarithms. It says of each entry $v$ of a word that $c(|x|+v+1) \le 2^w$,
which makes every entry a word and leaves room for the constant multiple
of the length that bounds the addresses and the step count. Entries are not bounded by
the length in general: a parameter, a weight or a deadline may be any number at all, so
the claim quantifies over the entries instead of assuming they are small.

A reduction's *output* has to fit as well. A machine at word length $w$ reduces what it
writes modulo $2^w$, so a word whose image does not fit is one the program cannot emit;
the admissible set therefore constrains the image too. Like every fitting condition here
this restricts the inputs rather than appearing as a hypothesis: as a hypothesis it would
be empty, since no word length accommodates every encoding of a fixed instance at once.

The bound is `c * g k * (x.length + 1)`, elementary rather than asymptotic, with the
`+ 1` making it meaningful on the empty word. Its dependence on the length is linear,
where the usual definition of FPT allows $g(k)\,|x|^{O(1)}$, so both notions defined here
are the stricter ones: a problem that is fixed-parameter tractable in this sense is so in
the usual sense, and a reduction that meets this bound is an fpt-reduction in the usual
sense. A membership and a hardness proved against these definitions therefore imply their
standard forms. Nothing weaker is defined because nothing weaker is needed — the dynamic
program of Theorem 3 and the reduction of Theorem 1 both run within a linear bound.

`g` is an arbitrary function of the parameter: it bounds a fixed program's running time
rather than defining it, so no computability requirement on `g` is needed or intended.
Some presentations of FPT require $g$ to be computable; the definition here does not, and
the $g$ that Theorem 3 supplies is a closed-form expression in the parameter, so that
theorem meets the definitions that require it as well.

Only the timed notions are defined. Plain computability is the special case in which the
bound is unconstrained, and is not what any statement of this submission needs.
-/

namespace Lax888481.ParameterizedComplexity

open Lax808846.Ram Lax808846.RamComputes

/-- A parameterized problem: the words that encode an instance, which of them are
yes-instances, and the parameter each one carries. -/
structure Problem where
  /-- The words that encode an instance. A program may do anything on the others. -/
  Domain : Set (List ℕ)
  /-- The yes-instances. -/
  Yes : List ℕ → Prop
  /-- The parameter, read off the word. -/
  param : List ℕ → ℕ

/-- The word `x` fits at word length `w`, with room for `c` times its length: every
entry `v` of `x` satisfies `c * (x.length + v + 1) ≤ 2 ^ w`. -/
def Fits (c w : ℕ) (x : List ℕ) : Prop := ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w

open Classical in
/-- At every word length, the program decides `P` on every admissible word that fits,
within `c * g k * (|x| + 1)` instructions, where `k` is the word's parameter. It writes
`1` for a yes-instance and `0` for a no-instance. -/
def Decides (P : Problem) (prog : Program) (c : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ w : ℕ, ComputesInTime w prog
    {x | x ∈ P.Domain ∧ Fits c w x}
    (fun x => if P.Yes x then [1] else [0])
    (fun x => c * g (P.param x) * (x.length + 1))

/-- `P` is **fixed-parameter tractable**: one program and one constant decide it within
`c * g k * (|x| + 1)` instructions, for some function `g` of the parameter alone. -/
def FPT (P : Problem) : Prop := ∃ (prog : Program) (c : ℕ) (g : ℕ → ℕ), Decides P prog c g

/-- The map `f` is an fpt-reduction from `P` to `Q`, computed by `prog` within
`c * g k * (|x| + 1)` instructions and raising the parameter by at most `h`. -/
structure IsFptReduction (P Q : Problem) (f : List ℕ → List ℕ) (prog : Program)
    (c : ℕ) (g h : ℕ → ℕ) : Prop where
  /-- The image of an admissible word is admissible. -/
  maps_domain : ∀ x ∈ P.Domain, f x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (f x))
  /-- The new parameter is bounded by a function of the old one alone. -/
  param_le : ∀ x ∈ P.Domain, Q.param (f x) ≤ h (P.param x)
  /-- At every word length, the program computes `f` on every admissible word that fits
  and whose image fits, within the stated bound. -/
  time : ∀ w : ℕ, ComputesInTime w prog
    {x | x ∈ P.Domain ∧ Fits c w x ∧ Fits c w (f x)}
    f (fun x => c * g (P.param x) * (x.length + 1))

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop :=
  ∃ (f : List ℕ → List ℕ) (prog : Program) (c : ℕ) (g h : ℕ → ℕ),
    IsFptReduction P Q f prog c g h

@[inherit_doc] infix:50 " ≤fpt " => FptReduces

end Lax888481.ParameterizedComplexity
