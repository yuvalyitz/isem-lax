import Lax470956Proofs.SweepProg

/-!
The brute force, as a word RAM program: the commands.

When the table of the sweep cannot be addressed, the machine tries every schedule. A schedule
is a string of `n` digits in base `m + 1` (`Brute.schedOf`), kept in the array `asg` and
advanced like an odometer. For each string the program checks, from the word itself, that every
job sits on an eligible machine and that no two overlapping jobs share one, and it adds up the
weight, never letting the running total pass the threshold `W`.

Every test is written with arithmetic on the values `0` and `1`, or as a one-armed
conditional whose test is a single comparison, so that a pass costs the same whatever it finds.
-/

namespace Lax470956Proofs.BruteProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956Proofs.SweepProg

/-! ### Eligibility: Is Machine `va - 1` Among the Targets of Job `j`? -/

/-- One target of the job's block: does it name the machine the digit says? -/
def eligStep : Com :=
  .seq (.ite (.eq (add (.get "a" (add (V "T0") (add (V "o1") (V "e")))) (lit 1)) (V "va"))
      (set "fnd" (lit 1)) .skip)
    (bump "e")

def eligLoop : Com :=
  .seq (set "fnd" (lit 0)) (.seq (set "e" (lit 0)) (.while (.lt (V "e") (V "elen")) eligStep))

/-- The processing time of job `j`. -/
abbrev pOf (j : Expr) : Expr := .get "a" (add (lit 2) j)
/-- The deadline of job `j`. -/
abbrev dOf (j : Expr) : Expr := .get "a" (add (add (lit 2) (V "n")) j)
/-- The weight of job `j`. -/
abbrev wOf (j : Expr) : Expr := .get "a" (add (add (lit 2) (mul (lit 2) (V "n"))) j)

/-- Read one job's digit and its block of targets. -/
def jobFetch : Com :=
  .seq (.assign "va" (.get "asg" (V "j")))
    (.seq (.assign "o1" (.get "a" (add (V "O0") (V "j"))))
      (.seq (.assign "o2" (.get "a" (add (add (V "O0") (V "j")) (lit 1))))
        (.assign "elen" (sub (V "o2") (V "o1")))))

/-- Mark the schedule infeasible if the digit names a machine outside the block, and add
the weight if the job is scheduled. -/
def jobFold : Com :=
  .seq (set "ok" (sub (V "ok") (sub (cap (V "va") (lit 1)) (V "fnd"))))
    (.seq (.ite (.lt (lit 0) (V "va"))
        (set "acc" (cap (add (V "acc") (wOf (V "j"))) (V "W"))) .skip)
      (bump "j"))

/-- One job. -/
def jobStep2 : Com := .seq jobFetch (.seq eligLoop jobFold)

/-! ### Clashes: Two Overlapping Jobs on One Machine -/

/-- `1` when the digits agree, `0` otherwise. -/
abbrev eqFlag (e f : Expr) : Expr :=
  sub (lit 1) (cap (add (sub e f) (sub f e)) (lit 1))

/-- `1` when `e < f`, `0` otherwise. -/
abbrev ltFlag (e f : Expr) : Expr := cap (sub f e) (lit 1)

/-- The two jobs run on one machine and overlap: the digits agree and are not zero, and
each job starts before the other is due. Four flags, added, less three. -/
abbrev clashE : Expr :=
  sub (add (add (eqFlag (V "va") (V "vb")) (cap (V "va") (lit 1)))
      (add (ltFlag (V "sa") (V "db")) (ltFlag (V "sb") (V "da")))) (lit 3)

def pairStep : Com :=
  .seq (.assign "vb" (.get "asg" (V "b")))
    (.seq (.assign "db" (dOf (V "b")))
      (.seq (.assign "sb" (sub (V "db") (pOf (V "b"))))
        (.seq (set "ok" (sub (V "ok") clashE)) (bump "b"))))

/-- Read the job in hand: its digit, its deadline, its start. -/
def pairFetch : Com :=
  .seq (.assign "va" (.get "asg" (V "i")))
    (.seq (.assign "da" (dOf (V "i")))
      (.seq (.assign "sa" (sub (V "da") (pOf (V "i"))))
        (set "b" (add (V "i") (lit 1)))))

/-- The job in hand against every later one. -/
def pairInner : Com := .while (.lt (V "b") (V "n")) pairStep

/-- One job against every later one. -/
def pairOuterStep : Com := .seq pairFetch (.seq pairInner (bump "i"))

/-- Every job's digit against its block of targets. -/
def jobsLoop : Com := .seq (set "j" (lit 0)) (.while (.lt (V "j") (V "n")) jobStep2)

/-- Every pair of jobs. -/
def pairsLoop : Com := .seq (set "i" (lit 0)) (.while (.lt (V "i") (V "n")) pairOuterStep)

/-- Test the string in `asg`: `ok` ends `1` exactly when the schedule it reads is feasible,
and `acc` holds its weight, capped at `W`. -/
def evalOne : Com :=
  .seq (set "ok" (lit 1)) (.seq (set "acc" (lit 0)) (.seq jobsLoop pairsLoop))

/-! ### The Odometer -/

/-- One digit of the advance: add the carry; if the sum passes `m` the digit wraps to zero
and the carry moves on, otherwise the digit is the sum and the carry is spent. -/
def carryBody : Com :=
  .seq (.assign "tt" (add (.get "asg" (V "i")) (V "cy")))
    (.seq (set "cy" (sub (V "tt") (V "m")))
      (.seq (.ite (.lt (lit 0) (V "cy")) (.store "asg" (V "i") (lit 0))
          (.store "asg" (V "i") (V "tt")))
        (bump "i")))

/-- Add one to the string. The carry out of the last digit is `1` exactly when the string
was the last one, and the string is then all zeros again. -/
def carryLoop : Com :=
  .seq (set "cy" (lit 1)) (.seq (set "i" (lit 0)) (.while (.lt (V "i") (V "n")) carryBody))

/-- Record a success: `ans` becomes `1` when the string just tested was feasible and reached
the threshold. -/
def recordStep : Com :=
  .ite (.eq (V "ok") (lit 1)) (.ite (.eq (V "acc") (V "W")) (set "ans" (lit 1)) .skip) .skip

/-- The string was the last one exactly when the carry ran off its end. -/
def dnStep : Com := set "dn" (V "cy")

/-- Test a string, record a success, move on. -/
def bruteBody : Com :=
  .seq evalOne (.seq recordStep (.seq carryLoop dnStep))

/-- Try every string. -/
def bruteLoop : Com :=
  .seq (set "ans" (lit 0)) (.seq (set "dn" (lit 0))
    (.while (.eq (V "dn") (lit 0)) bruteBody))

/-- The brute force: answer `1` if some string reads a feasible schedule of weight `W`. -/
def bruteWork : Com := .seq bruteLoop (.write (V "ans"))

end Lax470956Proofs.BruteProg
