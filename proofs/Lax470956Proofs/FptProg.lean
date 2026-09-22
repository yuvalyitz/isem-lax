import Lax470956Proofs.BruteRun

/-!
The second program of Theorem 3: the one that decides on every word.

The sweep needs a table with `(p_max + 1) ^ m` entries, and a word whose entries fit into words
need not leave room for one. The program therefore measures first: it computes
`min ((p_max + 1) ^ m) (|x| + 1)` without ever forming a number larger than `|x| + 1`, and
compares it with `|x|`. When the table is no larger than the word, the sweep runs; otherwise the
word is larger than the table's size, which is a function of the parameter alone, and the
program tries every schedule.
-/

namespace Lax470956Proofs.FptProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956Proofs.SweepProg Lax470956Proofs.BruteProg

/-- One factor of the capped power: if the table so far, times `p_max + 1`, still fits under
the length of the word, multiply; otherwise it has passed the length and stays one past it.
The test divides rather than multiplies, so that no intermediate value exceeds the word. -/
def capBody : Com :=
  .seq (.ite (.lt (V "qq") (V "Sc")) (set "Sc" (add (V "L") (lit 1)))
      (set "Sc" (mul (V "Sc") (add (V "P") (lit 1)))))
    (bump "i")

/-- The quotient the test compares against, and the first power. -/
def capInit : Com :=
  .seq (set "qq" (dv (V "L") (add (V "P") (lit 1)))) (set "Sc" (lit 1))

/-- `Sc := min ((p_max + 1) ^ m) (|x| + 1)`. -/
def capLoop : Com :=
  .seq capInit (.seq (set "i" (lit 0)) (.while (.lt (V "i") (V "m")) capBody))

/-- The answer when there is no machine or no job. -/
def degen : Com := .ite (.eq (V "W") (lit 0)) (.write (lit 1)) (.write (lit 0))

/-- The main work: find `p_max`, measure the table, and either sweep or try everything. -/
def mainWork2 : Com :=
  .seq pmaxLoop (.seq capLoop (.ite (.lt (V "L") (V "Sc")) bruteWork mainWork))

/-- The whole program. -/
def com2 : Com :=
  .seq ReadHdr.readWord (.seq header
    (.ite (.eq (V "m") (lit 0)) degen
      (.ite (.eq (V "n") (lit 0)) degen mainWork2)))

/-- The layout: every scalar and array either branch names. -/
def layout2 : Layout :=
  ⟨["L", "rt", "rv", "n", "m", "W", "cap", "O0", "T0", "v", "j", "P", "S", "i", "dd",
    "ok", "nx", "Pm", "e", "kk", "hp", "ib", "jp", "cur", "nc0", "N3", "s", "c", "bst",
    "tp", "u", "del", "c2", "mi", "pj", "wj", "jb", "t", "k", "acc", "o1", "o2", "elen",
    "qq", "Sc", "fnd", "va", "vb", "db", "sb", "da", "sa", "b", "ans", "dn", "cy", "tt"],
   ["a", "pw", "occ", "fj", "nj", "st", "nx2", "ord", "dl", "nc", "V", "V2", "Vt", "asg"], 8⟩

theorem com2_ok : Com.Ok layout2 com2 := by
  simp [com2, mainWork2, capLoop, capInit, capBody, degen, mainWork, bruteWork, bruteLoop, bruteBody,
    evalOne, jobsLoop, jobStep2, jobFetch, eligLoop, eligStep, jobFold, pairsLoop,
    pairOuterStep, pairFetch, pairInner, pairStep, recordStep, carryLoop, carryBody, dnStep,
    ReadHdr.readWord, ReadHdr.readUpTo, ReadAll.readBody, header,
    pmaxLoop, pmaxBody, powLoop, powBody, bucketLoop, bucketBody, startLoop, startBody,
    scanLoop, scanBody, orderLoop, orderBody, emitStep, emitLoop, walkBody, blockLoop,
    openStep, sweepLoop,
    sweepBody, startJob, jobData, entryBody, entryLoop, closeBlock, bestLoop, bestBody, clearLoop,
    commitLoop, shiftLoop, shiftBody, zeroLoop, zeroLoopOf, zeroBodyOf, advLoop, advBody, commitBody,
    relaxLoop, relaxBody, takeLoop, takeBody, layout2, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq2 : layout2.const = 10 := by simp [Layout.const]

end Lax470956Proofs.FptProg
