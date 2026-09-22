import Lax470956.Scheduling
import Lax434930.PolynomialTime
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

/-!
---
title: Binary encoding of a scheduling instance
type: definition
---
A scheduling instance as a binary word, the representation classical complexity measures
running time against. A number is written as its binary digits preceded by its length in
unary, which makes the encoding self-delimiting; an instance is the number of jobs, the
number of machines, the three arrays of processing times, deadlines and weights, and the
$n \times m$ eligibility matrix, in that order.

# Formalization notes

This encoding exists beside the word encoding of `InstanceEncoding` and does not replace
it. They answer different questions. A word RAM is handed numbers and charges one
instruction per operation on them, so its input is a list of numbers and its running time
is measured in their count; a Turing machine is handed bits, so a claim of polynomial
time is a claim about the number of bits. The two statements of this submission that
quantify over all of NP are Turing-machine statements and use this encoding; the
fixed-parameter statement is a word RAM statement and uses the other.

Numbers are written in binary rather than unary. The difference is not cosmetic for a
hardness claim: under a unary encoding the input is exponentially longer, which makes a
polynomial-time reduction easier to achieve and the resulting hardness claim
correspondingly weaker — it would be a claim of *strong* NP-hardness only. Binary is
what the unqualified statement means.

The eligibility matrix is written in full, one bit per job-machine pair, rather than as
adjacency lists. At $nm$ bits it is within a polynomial of any other reasonable choice,
and polynomial time is invariant under polynomial changes of encoding; the matrix is the
simpler object and matches the encoding of a graph elsewhere in the archive.

The encoding need not be injective on instances that differ only in inaccessible data,
and nothing here claims it is. What the statements need is that it is computable in
polynomial time and that the reduction's image is determined, both of which are
obligations of the proof layer.
-/

namespace Lax470956.BinaryEncoding

open Lax470956.Scheduling Lax434930.PolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. The unary prefix makes the code self-delimiting. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An instance as a binary word: the two counts, the processing times, the deadlines,
the weights, and the eligibility matrix in row order. -/
def encodeInstance (I : Instance) : Word :=
  encodeNat I.jobs ++ encodeNat I.machines ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.p j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.d j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.w j)) ++
    (List.finRange I.jobs).flatMap
      (fun j => (List.finRange I.machines).map fun i => decide (i ∈ I.eligible j))

end Lax470956.BinaryEncoding
