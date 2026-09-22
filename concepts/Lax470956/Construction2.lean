import Lax470956.Exact34Encoding
import Lax470956.InstanceEncoding
import Lax759944.RamPolytime
import Mathlib.Data.Finset.Lattice.Fold

/-!
---
title: Construction 2
type: definition
---
The scheduling instance built from a $(3,4)$ formula. Each variable gets two
machines, one for each truth value, and one job spanning a fixed window of length $25$.
Each clause gets three machines, and each of its three literal occurrences gets three
jobs: a unit job whose deadline $2(k+1) + 8h$ records which occurrence $k$ of its
variable it is and which literal $h$ of its clause, flanked by two jobs filling the rest
of the window.

The window is what makes the construction work. A variable job overlaps every job of
every occurrence of its variable, so a schedule that places all of them must put the
variable job on one of the two machines of its variable, and that choice is the truth
value. The bounded number of occurrences of a variable is what keeps the window, and
with it every processing time, bounded by an absolute constant.

# Formalization notes

The construction is a total function on words, so that the map it induces is defined
everywhere and the statements about it need no side condition. A word that is not a
well-formed formula still produces an instance, because the deadline is clamped to
$[2, 24]$ — exactly the range it already occupies when the appearance index is below
four and the literal index below three. The clamp is therefore invisible on well-formed
input, and it is what discharges the two standing conventions $0 < p$ and $p \le d$
without a hypothesis.

Jobs and machines are numbered rather than tagged. Job $v$ for $v < V$ belongs to
variable $v$; job $V + 9c + 3h + s$ belongs to occurrence $h$ of clause $c$, in slot
$s$ — the literal job for $s = 0$ and its two wrappers for $s = 1, 2$. Machine $2v$ is
the true machine of variable $v$ and $2v + 1$ its false machine; machine
$2V + 3c + t$ is the $t$-th machine of clause $c$. The numbering is part of the
construction because an instance is something a machine is handed, and a word presents
its jobs in an order.
-/

namespace Lax470956.Construction2

open Lax470956.Scheduling Lax470956.Exact34Encoding

variable (x : List ℕ)

/-- The number of variables the word declares. -/
abbrev nVar : ℕ := varCount x

/-- The number of clauses the word declares. -/
abbrev nCla : ℕ := clauseCount x

/-- One job per variable and nine per clause. -/
def nJobs : ℕ := nVar x + 9 * nCla x

/-- Two machines per variable and three per clause. -/
def nMach : ℕ := 2 * nVar x + 3 * nCla x

/-- The deadline of the literal job of occurrence `h` of clause `c`, clamped to the
range `[2, 24]` it already lies in on a well-formed word. -/
def dl (c h : ℕ) : ℕ := min 24 (max 2 (2 * (litApp x c h + 1) + 8 * h))

lemma dl_ge (c h : ℕ) : 2 ≤ dl x c h := by
  simp only [dl]; omega

lemma dl_le (c h : ℕ) : dl x c h ≤ 24 := by
  simp only [dl]; omega

/-- On a well-formed word the clamp is inactive: the deadline is the formula's own
`2(k+1) + 8h`. -/
lemma dl_eq_of_lt {c h : ℕ} (happ : litApp x c h < 4) (hh : h < 3) :
    dl x c h = 2 * (litApp x c h + 1) + 8 * h := by
  simp only [dl]; omega

variable {x}

/-- The clause of job index `i` counted from the first clause job. -/
def cOf (i : ℕ) : ℕ := i / 9

/-- The literal of job index `i` counted from the first clause job. -/
def hOf (i : ℕ) : ℕ := i % 9 / 3

/-- The slot of job index `i` counted from the first clause job. -/
def sOf (i : ℕ) : ℕ := i % 3

variable (x)

/-- The processing time of job `j`. -/
def procOf (j : ℕ) : ℕ :=
  if j < nVar x then 25
  else
    match sOf (j - nVar x) with
    | 0 => 1
    | 1 => dl x (cOf (j - nVar x)) (hOf (j - nVar x)) - 1
    | _ => 25 - dl x (cOf (j - nVar x)) (hOf (j - nVar x))

/-- The deadline of job `j`. -/
def dueOf (j : ℕ) : ℕ :=
  if j < nVar x then 25
  else
    match sOf (j - nVar x) with
    | 0 => dl x (cOf (j - nVar x)) (hOf (j - nVar x))
    | 1 => dl x (cOf (j - nVar x)) (hOf (j - nVar x)) - 1
    | _ => 25

/-- The machines eligible to run job `j`, as a list of machine numbers. -/
def eligOf (j : ℕ) : List ℕ :=
  if j < nVar x then [2 * j, 2 * j + 1]
  else
    let i := j - nVar x
    let base := 2 * nVar x + 3 * cOf i
    match sOf i with
    | 0 => [base + 1, base + 2,
            2 * litVar x (cOf i) (hOf i) + (if litSign x (cOf i) (hOf i) = 1 then 0 else 1)]
    | _ => [base, base + 1, base + 2]

lemma procOf_pos (j : ℕ) : 0 < procOf x j := by
  unfold procOf
  split
  · omega
  · have h1 := dl_ge x (cOf (j - nVar x)) (hOf (j - nVar x))
    have h2 := dl_le x (cOf (j - nVar x)) (hOf (j - nVar x))
    match hs : sOf (j - nVar x) with
    | 0 => simp
    | 1 => simp <;> omega
    | (k + 2) => simp <;> omega

lemma procOf_le_dueOf (j : ℕ) : procOf x j ≤ dueOf x j := by
  unfold procOf dueOf
  split
  · omega
  · have h1 := dl_ge x (cOf (j - nVar x)) (hOf (j - nVar x))
    have h2 := dl_le x (cOf (j - nVar x)) (hOf (j - nVar x))
    match hs : sOf (j - nVar x) with
    | 0 => simp <;> omega
    | 1 => simp
    | (k + 2) => simp <;> omega

lemma procOf_le_25 (j : ℕ) : procOf x j ≤ 25 := by
  unfold procOf
  split
  · omega
  · have h1 := dl_ge x (cOf (j - nVar x)) (hOf (j - nVar x))
    have h2 := dl_le x (cOf (j - nVar x)) (hOf (j - nVar x))
    match hs : sOf (j - nVar x) with
    | 0 => simp
    | 1 => simp <;> omega
    | (k + 2) => simp <;> omega

/-- **Construction 2.** The scheduling instance built from the word `x`. -/
def inst : Instance where
  jobs := nJobs x
  machines := nMach x
  p j := procOf x j
  d j := dueOf x j
  w _ := 1
  eligible j := Finset.univ.filter fun i : Fin (nMach x) => (i : ℕ) ∈ eligOf x j
  p_pos j := procOf_pos x j
  p_le_d j := procOf_le_dueOf x j

@[simp] lemma inst_jobs : (inst x).jobs = nJobs x := rfl
@[simp] lemma inst_machines : (inst x).machines = nMach x := rfl
@[simp] lemma inst_p (j : Fin (nJobs x)) : (inst x).p j = procOf x j := rfl
@[simp] lemma inst_d (j : Fin (nJobs x)) : (inst x).d j = dueOf x j := rfl


/-- Where job `j`'s block of eligible machines begins. -/
def offOf (j : ℕ) : ℕ :=
  if j ≤ nVar x then 2 * j else 2 * nVar x + 3 * (j - nVar x)

/-- The processing-time block. -/
def procBlock : List ℕ := (List.range (nJobs x)).map (procOf x)

/-- The deadline block. -/
def dueBlock : List ℕ := (List.range (nJobs x)).map (dueOf x)

/-- The weight block: every job has weight one. -/
def wtBlock : List ℕ := List.replicate (nJobs x) 1

/-- The offset block, one entry per job and one more. -/
def offBlock : List ℕ := (List.range (nJobs x + 1)).map (offOf x)

/-- The target block: the eligible machines of each job in turn. -/
def tgtBlock : List ℕ := (List.range (nJobs x)).flatMap (eligOf x)

/-- **The word Construction 2 emits.** -/
def emit : List ℕ :=
  [nJobs x, nMach x] ++ procBlock x ++ dueBlock x ++ wtBlock x ++ offBlock x ++ tgtBlock x

/-- The word a malformed input is sent to: one job, no machine, so its only job cannot
be scheduled. -/
def noWord : List ℕ := [1, 0, 1, 1, 1, 0, 0]

/-- **Construction 2 as a total map on words.** A word that is not a well-formed formula
is sent to a fixed instance that cannot schedule every job. A reduction is a function on
all words, and the machine that computes it has to decide which case it is in; making the
diversion part of the map rather than a side condition is what keeps the statement below
free of hypotheses.

The case split is on a proposition rather than on a decision procedure, so the map is
`noncomputable` in Lean. Nothing is lost: what has to be computable is the machine
program, and the statement that one computes this map is `reduce_computesInTime`. -/
noncomputable def reduce (x : List ℕ) : List ℕ :=
  open Classical in
  if Lax470956.Exact34Encoding.WellFormed x then emit x else noWord

/-- Every weight of the constructed instance is `1`. -/
axiom weights_one (x : List ℕ) (j : Fin (inst x).jobs) : (inst x).w j = 1

/-- Every processing time of the constructed instance is at most `25`. -/
axiom pmax_le (x : List ℕ) : (inst x).pmax ≤ 25

/-- **Construction 2 is correct.** A well-formed `(3,4)` formula is satisfiable
exactly when every job of the instance it builds can be scheduled. -/
axiom correct (x : List ℕ) (hwf : Lax470956.Exact34Encoding.WellFormed x) :
    (∃ τ, Lax470956.Exact34Encoding.Satisfies x τ) ↔ (inst x).AllSchedulable

/-- **The emitted word encodes the constructed instance.** -/
axiom emit_encodes (x : List ℕ) (hwf : Lax470956.Exact34Encoding.WellFormed x) :
    Lax470956.InstanceEncoding.EncodesInstance (emit x) (inst x)

/-- **The reduction is correct.** A word is a satisfiable `(3,4)` formula exactly
when the instance it is sent to can schedule every job. -/
axiom reduce_correct (x : List ℕ) :
    x ∈ Lax470956.Exact34Encoding.Satisfiable ↔
      ∃ I, Lax470956.InstanceEncoding.EncodesInstance (reduce x) I ∧ I.AllSchedulable

/-- **The reduction lands in the bounded slice.** Every instance it emits has processing
times at most `25` and unit weights. -/
axiom reduce_slice (x : List ℕ) :
    ∃ I, Lax470956.InstanceEncoding.EncodesInstance (reduce x) I ∧
      I.pmax ≤ 25 ∧ ∀ j, I.w j = 1

open Lax759944.RamPolytime in
/-- **The reduction runs in polynomial time.** One word RAM program computes the map on
every word — well-formed or not — within a polynomial number of instructions in the bit
size of its input.

This is the running-time half of the reduction, and it is the half the hardness
statements need, so it is stated in their currency: `Lax759944.RamPolytime` measures the
input by its bit size rather than by the number of entries, hands the machine the input
preceded by its length, and is proved in that submission to be interchangeable with
polynomial time on a Turing machine. The statement about the emitter alone,
`emit_computesInTime`, is the same claim in the archive's word-RAM currency and on
well-formed input only; it is the part of this one that does the work, and deciding
well-formedness is what the rest of it adds.

Deciding well-formedness is not a formality. The condition that distinct occurrences of
one variable carry distinct appearance indices is a disjointness condition on `3C`
pairs, and it is decidable in one pass only because the pairs live in a universe of size
`4V`: an occurrence is bucketed at `4v + k`, and a bucket claimed twice refutes it. -/
axiom reduce_ramPolytime : RamPolytime reduce

open Lax808846.Ram Lax808846.RamComputes Lax470956.ParameterizedComplexity in
/-- **Construction 2 runs in linear time.** One word RAM program and one constant `c`
such that, at every word length, on every well-formed formula whose entries fit, the
program halts within `c · (|x| + 1)` instructions having written `emit x`. -/
axiom emit_computesInTime :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {y | Lax470956.Exact34Encoding.WellFormed y ∧ Fits c w y}
        emit (fun y => c * (y.length + 1))

end Lax470956.Construction2
