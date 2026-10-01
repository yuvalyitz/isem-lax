import Lax888481Proofs.ReadHdr
import Lax888481Proofs.Radix
import Lax888481Proofs.BlockWalk
import Lax888481Proofs.FreeDP

/-!
The sweep, as a word RAM program: the commands.

Eight passes. Read the word; read off its header; find the largest processing time; build
the powers of `p_max + 1` that index the table; bucket the jobs by deadline; find, for
every deadline, whether it starts a block and which deadline follows it inside its block;
walk the blocks, writing out the jobs in the order the sweep wants them; and sweep.
-/

namespace Lax888481Proofs.SweepProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev lit (n : ℕ) : Expr := .lit n
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev dv (e f : Expr) : Expr := .bin .div e f
/-- Remainder, built from division: there is no remainder operation. -/
abbrev md (e f : Expr) : Expr := sub e (mul (dv e f) f)
abbrev bump (s : String) : Com := .assign s (add (V s) (lit 1))
abbrev set (s : String) (e : Expr) : Com := .assign s e

/-! ### The Header -/

def header : Com :=
  .seq (set "n" (.get "a" (lit 0)))
    (.seq (set "m" (.get "a" (lit 1)))
      (.seq (set "W" (.get "a" (sub (V "L") (lit 1))))
        (.seq (set "cap" (V "W"))
          (.seq (set "O0" (add (lit 2) (mul (lit 3) (V "n"))))
            (set "T0" (add (lit 3) (mul (lit 4) (V "n"))))))))

/-! ### The Largest Processing Time -/

/-- The larger of two values, with truncated subtraction. -/
abbrev mx (e f : Expr) : Expr := add e (sub f e)

/-- Capping, with truncated subtraction: `a - (a - b)` is the smaller of the two. -/
abbrev cap (e f : Expr) : Expr := sub e (sub e f)

def pmaxBody : Com :=
  .seq (.assign "v" (.get "a" (add (lit 2) (V "j"))))
    (.seq (set "P" (mx (V "P") (V "v"))) (bump "j"))

def pmaxLoop : Com :=
  .seq (set "P" (lit 0)) (.seq (set "j" (lit 0)) (.while (.lt (V "j") (V "n")) pmaxBody))

/-! ### The Powers That Index the Table -/

def powBody : Com :=
  .seq (.store "pw" (V "i") (V "S")) (.seq (set "S" (mul (V "S") (add (V "P") (lit 1)))) (bump "i"))

def powLoop : Com :=
  .seq (set "S" (lit 1)) (.seq (set "i" (lit 0)) (.while (.lt (V "i") (V "m")) powBody))

/-! ### The Jobs of Each Deadline -/

def bucketBody : Com :=
  .seq (.assign "dd" (.get "a" (add (add (lit 2) (V "n")) (V "j"))))
    (.seq (.store "occ" (V "dd") (lit 1))
      (.seq (.store "nj" (V "j") (.get "fj" (V "dd")))
        (.seq (.store "fj" (V "dd") (add (V "j") (lit 1))) (bump "j"))))

def bucketLoop : Com :=
  .seq (set "j" (lit 0)) (.while (.lt (V "j") (V "n")) bucketBody)

/-! ### Block Starts, and the Next Deadline Inside a Block -/

/-- The cell `occ` is read below `dd` — a violation of the block start — and above it,
counting down, so that the last write wins and `nx` ends at the nearest occupied point.
Both updates are written with arithmetic rather than a test. -/
def scanBody : Com :=
  .seq (set "ok" (mul (V "ok") (sub (lit 1) (.get "occ" (sub (sub (V "dd") (lit 1)) (V "e"))))))
    (.seq (set "nx"
        (add (mul (.get "occ" (sub (add (V "dd") (V "Pm")) (V "e")))
                  (sub (add (V "dd") (V "Pm")) (V "e")))
             (mul (sub (lit 1) (.get "occ" (sub (add (V "dd") (V "Pm")) (V "e")))) (V "nx"))))
      (bump "e"))

def scanLoop : Com :=
  .seq (set "e" (lit 0)) (.while (.lt (V "e") (V "Pm")) scanBody)

def startBody : Com :=
  .seq (.assign "dd" (.get "a" (add (add (lit 2) (V "n")) (V "j"))))
    (.seq (set "ok" (lit 1)) (.seq (set "nx" (lit 0))
      (.seq scanLoop
        (.seq (.store "st" (V "dd") (V "ok"))
          (.seq (.store "nx2" (V "dd") (V "nx")) (bump "j"))))))

def startLoop : Com :=
  .seq (set "Pm" (sub (V "P") (lit 1)))
    (.seq (set "j" (lit 0)) (.while (.lt (V "j") (V "n")) startBody))

/-! ### Walking the Blocks -/

/-- Write out one job of the deadline in hand. -/
def emitStep : Com :=
  .seq (.store "ord" (V "kk") (sub (V "jp") (lit 1)))
    (.seq (.store "dl" (V "kk") (V "cur"))
      (.seq (.store "nc" (V "kk") (V "nc0"))
        (.seq (set "nc0" (lit 0))
          (.seq (.assign "jp" (.get "nj" (sub (V "jp") (lit 1)))) (bump "kk")))))

/-- Write out every job of the deadline in hand. -/
def emitLoop : Com :=
  .seq (.assign "jp" (.get "fj" (V "cur")))
    (.while (.lt (lit 0) (V "jp")) emitStep)

/-- One turn of the walk along a block. -/
def walkBody : Com :=
  .seq emitLoop
    (.ite (.eq (.get "nx2" (V "cur")) (lit 0)) (set "ib" (lit 0))
      (.assign "cur" (.get "nx2" (V "cur"))))

/-- Walk the block whose first deadline is in `cur`. -/
def blockLoop : Com :=
  .seq (set "ib" (lit 1)) (.while (.eq (V "ib") (lit 1)) walkBody)

/-- If the job at `hp` is the last one of a deadline that starts a block, walk that
block. -/
def openStep : Com :=
  .seq (.assign "dd" (.get "a" (add (add (lit 2) (V "n")) (V "hp"))))
    (.ite (.eq (.get "st" (V "dd")) (lit 1))
      (.ite (.eq (.get "fj" (V "dd")) (add (V "hp") (lit 1)))
        (.seq (.assign "cur" (V "dd")) (.seq (set "nc0" (lit 1)) blockLoop))
        .skip)
      .skip)

def orderBody : Com := .seq openStep (bump "hp")

def orderLoop : Com :=
  .seq (set "kk" (lit 0)) (.seq (set "hp" (lit 0))
    (.while (.lt (V "hp") (V "n")) orderBody))

/-! ### The sweep

The table is `V`; `V2` is the table being built for the job in hand, and `Vt` the table
being built as time advances. An entry is `0` where the configuration is unreachable and
`1 + v` where `v` is the best weight reaching it, capped. -/

def bestBody : Com :=
  .seq (.ite (.lt (V "bst") (.get "V" (V "c"))) (set "bst" (.get "V" (V "c"))) .skip) (bump "c")

/-- The best entry of `V`, into `bst`. -/
def bestLoop : Com :=
  .seq (set "bst" (lit 0)) (.seq (set "c" (lit 0)) (.while (.lt (V "c") (V "S")) bestBody))

/-- Zero one cell of the table `nm`. -/
def zeroBodyOf (nm : String) : Com := .seq (.store nm (V "c") (lit 0)) (bump "c")

/-- Zero the table `nm`. -/
def zeroLoopOf (nm : String) : Com :=
  .seq (set "c" (lit 0)) (.while (.lt (V "c") (V "S")) (zeroBodyOf nm))

/-- Reset the table to the empty configuration at time zero. -/
def clearLoop : Com :=
  .seq (zeroLoopOf "V") (.seq (.store "V" (lit 0) (lit 1)) (set "tp" (lit 0)))

def zeroLoop : Com := zeroLoopOf "Vt"

/-- One digit of the advance: `u := min (dig c i + del) P`, accumulated into `c2`. -/
def advBody : Com :=
  .seq (.assign "u" (md (dv (V "c") (.get "pw" (V "i"))) (add (V "P") (lit 1))))
    (.seq (set "u" (cap (add (V "u") (V "del")) (V "P")))
      (.seq (set "c2" (add (V "c2") (mul (V "u") (.get "pw" (V "i"))))) (bump "i")))

def advLoop : Com :=
  .seq (set "c2" (lit 0)) (.seq (set "i" (lit 0)) (.while (.lt (V "i") (V "m")) advBody))

def shiftBody : Com :=
  .seq advLoop
    (.seq (.store "Vt" (V "c2") (mx (.get "Vt" (V "c2")) (.get "V" (V "c")))) (bump "c"))

def shiftLoop : Com :=
  .seq zeroLoop (.seq (set "c" (lit 0)) (.while (.lt (V "c") (V "S")) shiftBody))

def commitBody : Com :=
  .seq (.store "V" (V "c") (.get "Vt" (V "c"))) (.seq (.store "V2" (V "c") (.get "Vt" (V "c"))) (bump "c"))

/-- Time has advanced: install the new table as both the current one and the one being
built for the job in hand. -/
def commitLoop : Com :=
  .seq shiftLoop (.seq (set "c" (lit 0)) (.while (.lt (V "c") (V "S")) commitBody))

def relaxBody : Com :=
  .seq (.ite (.lt (lit 0) (.get "V" (V "c")))
      (.seq (.assign "u" (md (dv (V "c") (.get "pw" (V "mi"))) (add (V "P") (lit 1))))
        (.ite (.lt (V "u") (V "pj")) .skip
          (.seq (.assign "c2" (sub (V "c") (mul (V "u") (.get "pw" (V "mi")))))
            (.seq (.assign "v" (cap (add (.get "V" (V "c")) (V "wj")) (add (V "cap") (lit 1))))
              (.store "V2" (V "c2") (mx (.get "V2" (V "c2")) (V "v")))))))
      .skip)
    (bump "c")

/-- Place the job in hand on machine `mi`, everywhere it fits. -/
def relaxLoop : Com :=
  .seq (set "c" (lit 0)) (.while (.lt (V "c") (V "S")) relaxBody)

def takeBody : Com := .seq (.store "V" (V "c") (.get "V2" (V "c"))) (bump "c")

/-- The job in hand is done with. -/
def takeLoop : Com :=
  .seq (set "c" (lit 0)) (.while (.lt (V "c") (V "S")) takeBody)

/-- Close a block: add its best to the running total, capped. -/
def closeBlock : Com :=
  .seq bestLoop
    (.seq (set "acc" (add (V "acc") (sub (V "bst") (lit 1))))
      (.ite (.lt (V "cap") (V "acc")) (set "acc" (V "cap")) .skip))

/-- Set the table up for the job in hand: close the block if it starts one, then let
time run to its deadline. -/
def startJob : Com :=
  .seq (.assign "jb" (.get "ord" (V "k")))
    (.seq (.assign "t" (.get "dl" (V "k")))
      (.seq (.ite (.eq (.get "nc" (V "k")) (lit 1)) (.seq closeBlock clearLoop) .skip)
        (.seq (.assign "del" (sub (V "t") (V "tp")))
          (.seq commitLoop (.assign "tp" (V "t"))))))

/-- Read off the job in hand: its eligibility block, its processing time, its weight. -/
def jobData : Com :=
  .seq (.assign "o1" (.get "a" (add (V "O0") (V "jb"))))
    (.seq (.assign "o2" (.get "a" (add (add (V "O0") (V "jb")) (lit 1))))
      (.seq (.assign "elen" (sub (V "o2") (V "o1")))
        (.seq (.assign "pj" (.get "a" (add (lit 2) (V "jb"))))
          (.assign "wj" (.get "a" (add (add (lit 2) (mul (lit 2) (V "n"))) (V "jb")))))))

def entryBody : Com :=
  .seq (.assign "mi" (.get "a" (add (V "T0") (add (V "o1") (V "e")))))
    (.seq relaxLoop (bump "e"))

/-- Try the job in hand on each machine it is eligible on. -/
def entryLoop : Com :=
  .seq (set "e" (lit 0)) (.while (.lt (V "e") (V "elen")) entryBody)

def sweepBody : Com :=
  .seq startJob (.seq jobData (.seq entryLoop (.seq takeLoop (bump "k"))))

def sweepLoop : Com :=
  .seq (set "acc" (lit 0)) (.seq (set "k" (lit 0)) (.seq clearLoop
    (.while (.lt (V "k") (V "n")) sweepBody)))

/-- The main work, once there is a machine. -/
def mainWork : Com :=
  .seq pmaxLoop (.seq powLoop (.seq bucketLoop (.seq startLoop (.seq orderLoop
    (.seq sweepLoop (.seq closeBlock
      (.ite (.lt (V "acc") (V "cap")) (.write (lit 0)) (.write (lit 1)))))))))

/-- The whole program: read, look at the header, and either answer at once or sweep. -/
def com : Com :=
  .seq ReadHdr.readWord (.seq header
    (.ite (.eq (V "m") (lit 0))
      (.ite (.eq (V "W") (lit 0)) (.write (lit 1)) (.write (lit 0)))
      (.ite (.eq (V "n") (lit 0))
        (.ite (.eq (V "W") (lit 0)) (.write (lit 1)) (.write (lit 0)))
        mainWork)))

/-! ### The Layout -/

def layout : Layout :=
  ⟨["L", "rt", "rv", "n", "m", "W", "cap", "O0", "T0", "v", "j", "P", "S", "i", "dd",
    "ok", "nx", "Pm", "e", "kk", "hp", "ib", "jp", "cur", "nc0", "N3", "s", "c", "bst",
    "tp", "u", "del", "c2", "mi", "pj", "wj", "jb", "t", "k", "acc", "o1", "o2", "elen"],
   ["a", "pw", "occ", "fj", "nj", "st", "nx2", "ord", "dl", "nc", "V", "V2", "Vt"], 8⟩

theorem com_ok : Com.Ok layout com := by
  simp [com, mainWork, ReadHdr.readWord, ReadHdr.readUpTo, ReadAll.readBody, header,
    pmaxLoop, pmaxBody, powLoop, powBody, bucketLoop, bucketBody, startLoop, startBody,
    scanLoop, scanBody, orderLoop, orderBody, emitStep, emitLoop, walkBody, blockLoop,
    openStep, sweepLoop,
    sweepBody, startJob, jobData, entryBody, entryLoop, closeBlock, bestLoop, bestBody, clearLoop,
    commitLoop, shiftLoop, shiftBody, zeroLoop, zeroLoopOf, zeroBodyOf, advLoop, advBody, commitBody,
    relaxLoop, relaxBody, takeLoop, takeBody, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by simp [Layout.const]

end Lax888481Proofs.SweepProg
