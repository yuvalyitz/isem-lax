import Lax470956.ParameterizedComplexity

/-!
---
title: Word Encoding of a (3,4) Formula
type: definition
---
A $(3,4)$ formula is handed to a word random access machine as a word of numbers:
the number of variables, the number of clauses, then three blocks of three numbers per
clause, one block per literal, giving the variable it mentions, whether the occurrence is
positive, and which of the four occurrences of that variable it is.

# Formalization Notes

"Every variable occurs at most four times" is split into the two consequences the
two halves of the theorem actually use. `app_inj` — distinct occurrences of one variable
carry distinct appearance indices — is what the *correctness* of the reduction needs: it
makes the deadlines of one variable's occurrences pairwise distinct. `var_le` is what its
*running time* needs: without a bound tying the number of variables to the length of the
word, a two-entry word could declare $2^{100}$ variables, and the reduction would have to
emit that many jobs. Requiring surjectivity of the appearance index would give both, and
more than either needs.

The appearance index is part of the input rather than something a reader computes. It is
what the reduction of Theorem 2 turns into a deadline, and requiring it to be supplied
and to be consistent is what makes the deadlines of one variable's occurrences distinct.
That all four indices actually occur is never used, and is not required here; what is
required instead is the weaker `var_le`, which is the part of the counting a reduction
running in bounded time cannot do without.

A formula is presented directly, not as a satisfying assignment or any other certificate:
the yes-instances are the satisfiable words, and satisfiability is quantified over
assignments to the variables the word declares.

Sign bits are numbers, `1` for a positive occurrence and anything else for a negative
one, because a word RAM holds numbers. Reading a sign is then a comparison, as the emitted machine does.
-/

namespace Lax470956.Exact34Encoding

/-- The number of variables declared by a word: its first entry. -/
def varCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of clauses declared by a word: its second entry. -/
def clauseCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The variable of literal `h` of clause `c`. -/
def litVar (x : List ℕ) (c h : ℕ) : ℕ := x.getD (2 + 9 * c + 3 * h) 0

/-- The sign of literal `h` of clause `c`: `1` when the occurrence is positive. -/
def litSign (x : List ℕ) (c h : ℕ) : ℕ := x.getD (2 + 9 * c + 3 * h + 1) 0

/-- Which of the four occurrences of its variable literal `h` of clause `c` is. -/
def litApp (x : List ℕ) (c h : ℕ) : ℕ := x.getD (2 + 9 * c + 3 * h + 2) 0

/-- The word `x` is a `(3,4)` formula: two header entries followed by nine
numbers per clause, every variable in range, every appearance index below four,
distinct occurrences of one variable carrying distinct appearance indices, and no more
variables declared than there are literal slots to hold them. -/
structure WellFormed (x : List ℕ) : Prop where
  /-- The word consists of the header and three numbers per literal. -/
  length_eq : x.length = 2 + 9 * clauseCount x
  /-- Every literal mentions a declared variable. -/
  var_lt : ∀ c < clauseCount x, ∀ h < 3, litVar x c h < varCount x
  /-- Every appearance index is one of four. -/
  app_lt : ∀ c < clauseCount x, ∀ h < 3, litApp x c h < 4
  /-- Every declared variable occurs in some clause. There are `3C` literal slots, so a
  formula in which every variable occurs has at most `3C` of them. -/
  var_le : varCount x ≤ 3 * clauseCount x
  /-- Distinct occurrences of one variable carry distinct appearance indices. -/
  app_inj : ∀ c < clauseCount x, ∀ h < 3, ∀ c' < clauseCount x, ∀ h' < 3,
    litVar x c h = litVar x c' h' → litApp x c h = litApp x c' h' → c = c' ∧ h = h'

/-- The assignment `τ` satisfies the formula `x`: every clause owns a literal whose sign
agrees with `τ`. -/
def Satisfies (x : List ℕ) (τ : ℕ → Bool) : Prop :=
  ∀ c < clauseCount x, ∃ h < 3, (litSign x c h = 1) = τ (litVar x c h)

/-- The words encoding a `(3,4)` formula. -/
def Formulas : Set (List ℕ) := {x | WellFormed x}

/-- **(3,4)-SAT**, as a set of words. -/
def Satisfiable : Set (List ℕ) := {x | WellFormed x ∧ ∃ τ, Satisfies x τ}

end Lax470956.Exact34Encoding
