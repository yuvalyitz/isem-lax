import Lax470956.Scheduling

/-!
---
title: Word encoding of a scheduling instance
type: definition
---
A scheduling instance is handed to a word random access machine as a word of numbers:
the number $n$ of jobs, the number $m$ of machines, then the $n$ processing times, the
$n$ deadlines, the $n$ weights, then $n+1$ offsets and a target array listing, for each
job in turn, the machines eligible to run it. The offsets say where each job's block of
eligible machines begins, the first being $0$ and the last the length of the target
array. A decision instance appends the threshold $W$ as a final entry.

# Formalization notes

The eligible sets are in the same compressed sparse row form that presents a graph to a
machine elsewhere in the archive, for the same reason: it is the adjacency-array format
an algorithm would actually be handed, with nothing precomputed. The blocks are not
required to be sorted and repetitions are not forbidden. Leaving those conditions out
admits more words and therefore strengthens, rather than weakens, every claim about
programs reading the format.

Here magnitudes stop being free. The processing times, deadlines
and weights are entries of the word, so a claim about a program reading it has to say
that they are words — which the fitting conditions of `ParameterizedComplexity` do,
once, as an explicit inequality against `2 ^ w`. A size measure that counted only the
number of jobs and machines would make the weights of a reduction's output invisible,
and a running time stated against it would not be a claim about anything a machine does.

Cells are read with `List.getD`, which returns `0` outside the word; the length
condition pins the word down completely, so the default is never reached at a position
the other conditions constrain. Unlike a graph encoding, the length is not determined by
the header alone — the target array is as long as the last offset says — so
`length_eq` reads that offset rather than a declared edge count.

The threshold is appended last, so that the instance block sits at the same offsets
whether or not a threshold follows it, and the split of the word into the two parts is
determined by the word rather than chosen.
-/

namespace Lax470956.InstanceEncoding

open Lax470956.Scheduling

/-- The number of jobs declared by a word: its first entry. -/
def jobCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of machines declared by a word: its second entry. -/
def machineCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The processing time of job `j`: the processing times follow the two header
entries. -/
def proc (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + j) 0

/-- The deadline of job `j`: the deadlines follow the processing times. -/
def due (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + jobCount x + j) 0

/-- The weight of job `j`: the weights follow the deadlines. -/
def wt (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + 2 * jobCount x + j) 0

/-- The `i`-th offset: the `n+1` offsets follow the weights. -/
def offset (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + 3 * jobCount x + i) 0

/-- The `t`-th entry of the target array, which follows the offsets. -/
def target (x : List ℕ) (t : ℕ) : ℕ := x.getD (3 + 4 * jobCount x + t) 0

/-- The word `x` encodes the instance `I`. -/
structure EncodesInstance (x : List ℕ) (I : Instance) : Prop where
  /-- The word declares `I`'s jobs. -/
  jobCount_eq : jobCount x = I.jobs
  /-- The word declares `I`'s machines. -/
  machineCount_eq : machineCount x = I.machines
  /-- The word consists of the two header entries, the three arrays of one number per
  job, the `n+1` offsets, and a target array as long as the last offset says. -/
  length_eq : x.length = 3 + 4 * I.jobs + offset x I.jobs
  /-- The processing times are `I`'s. -/
  proc_eq : ∀ j : Fin I.jobs, proc x j = I.p j
  /-- The deadlines are `I`'s. -/
  due_eq : ∀ j : Fin I.jobs, due x j = I.d j
  /-- The weights are `I`'s. -/
  wt_eq : ∀ j : Fin I.jobs, wt x j = I.w j
  /-- The block of the first job begins at the start of the target array. -/
  offset_zero : offset x 0 = 0
  /-- The offsets are nondecreasing, so they cut the target array into one block per
  job. -/
  offset_mono : ∀ j < I.jobs, offset x j ≤ offset x (j + 1)
  /-- Every entry of the target array is a machine. -/
  target_lt : ∀ t < offset x I.jobs, target x t < I.machines
  /-- The block of a job lists exactly its eligible machines. -/
  eligible_iff : ∀ (j : Fin I.jobs) (i : Fin I.machines),
    i ∈ I.eligible j ↔ ∃ t, offset x j ≤ t ∧ t < offset x (j + 1) ∧ target x t = i

/-- The word `x` presents the instance `I` together with the threshold `W`: an instance
block followed by the single entry `W`. -/
def EncodesDecisionInstance (x : List ℕ) (I : Instance) (W : ℕ) : Prop :=
  ∃ y, x = y ++ [W] ∧ EncodesInstance y I

/-- The words that encode a decision instance. -/
def DecisionInstances : Set (List ℕ) :=
  {x | ∃ I W, EncodesDecisionInstance x I W}

/-- The words that encode an instance, with no threshold. -/
def Instances : Set (List ℕ) := {x | ∃ I, EncodesInstance x I}

end Lax470956.InstanceEncoding
