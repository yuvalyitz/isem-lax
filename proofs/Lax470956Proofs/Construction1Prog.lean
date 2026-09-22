import Lax470956Proofs.Construction1Edges
import Lax470956Proofs.Construction1Rank
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic

/-!
Construction 1 as a word RAM program: the program.

The program reads the two counts, copies the rest of the word into an array so that the
offsets, targets and colours can be read again, and then prepares two tables. The first
is the rank of every vertex in the paper's order, obtained by sweeping the vertices once
for each colour and numbering them as they are met — `k · n` steps, which the budget of
a parameterized reduction allows. The second is the edge enumeration, obtained by one
scan of the target array with a pointer to the vertex that owns the current slot.

With the tables in hand it writes the six blocks of the instance encoding and the
threshold. Every block is one counted pass over the jobs, and every pass begins by
recomputing everything about job `j` — its two raw times, its weight and its eligible
machines — through the same command, so that the arithmetic of the construction is
verified once and the passes differ only in which of those numbers they write.
-/

namespace Lax470956Proofs.Construction1Prog

open Lax808846Proofs.Imp Lax808846Proofs.Compile

/-! ### Expression shorthands -/

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev dvd (e f : Expr) : Expr := .bin .div e f
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (add (V s) (.lit 1))

/-- The colour of the vertex held in `s`. -/
abbrev colOf (s : String) : Expr := .get "a" (add (V "cb") (V s))

/-! ### Reading the word -/

def readBody : Com :=
  .seq (.read "v") (.seq (.store "a" (V "t") (V "v")) (bump "t"))

def readLoop : Com := .seq (.assign "t" (.lit 0)) (.while (.lt (V "t") (V "L")) readBody)

/-! ### The rank table -/

/-- Step `i` of the sweep looks at vertex `i mod n` on behalf of colour `i / n`. -/
def rankBody : Com :=
  .seq (.assign "c" (dvd (V "i") (V "n")))
  (.seq (.assign "v" (sub (V "i") (mul (V "c") (V "n"))))
  (.seq (.ite (.eq (colOf "v") (V "c"))
          (.seq (bump "cnt") (.store "r" (V "v") (V "cnt"))) .skip)
        (bump "i")))

def rankLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "nk")) rankBody)

/-! ### The edge table -/

/-- One turn of the scan: inside the owner's block, look at the slot; at its end, move
the owner on. -/
def edgeBody : Com :=
  .seq (.ite (.lt (V "p") (.get "a" (add (V "u") (.lit 1))))
          (.seq (.assign "w" (.get "a" (add (V "tb") (V "p"))))
          (.seq (.ite (.lt (colOf "u") (colOf "w"))
                  (.seq (.store "eu" (V "E") (V "u"))
                  (.seq (.store "ev" (V "E") (V "w")) (bump "E"))) .skip)
                (bump "p")))
          (bump "u"))
       (bump "i")

def edgeLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "S")) edgeBody)

/-! ### Everything about job `j` -/

/-- `b(b-1)/2 + a`, the machine of the colour pair. -/
abbrev pairE (a b : Expr) : Expr :=
  add (dvd (mul b (sub b (.lit 1))) (.lit 2)) a

/-- A slot that carries no job. -/
def inert : Com :=
  .seq (.assign "rp" (.lit 1)) (.seq (.assign "rd" (.lit 1))
  (.seq (.assign "Wt" (.lit 0)) (.assign "EL" (.lit 0))))

/-- A vertex job for the vertex's own colour. -/
def vOwn : Com :=
  .seq (.assign "rp" (V "K"))
  (.seq (.assign "rd" (add (mul (V "K") (V "pz")) (.lit 1)))
  (.seq (.assign "Wt" (.lit 1)) (.assign "EL" (.lit 1))))

/-- A vertex job for another colour. -/
def vOther : Com :=
  .seq (.assign "rp" (.lit 1))
  (.seq (.assign "rd" (sub (mul (V "K") (V "pz")) (V "cc")))
  (.seq (.assign "Wt" (V "c1"))
  (.seq (.assign "EL" (.lit 2))
    (.ite (.lt (V "cc") (V "cz"))
      (.assign "E2" (pairE (V "cc") (V "cz")))
      (.assign "E2" (pairE (V "cz") (V "cc")))))))

/-- Which vertex and colour vertex job `j` is for. -/
def vDecode : Com :=
  .seq (.assign "z" (dvd (V "j") (V "k")))
  (.seq (.assign "cc" (sub (V "j") (mul (V "z") (V "k"))))
  (.seq (.assign "cz" (colOf "z"))
  (.seq (.assign "pz" (.get "r" (V "z")))
        (.assign "E1" (V "val")))))

/-- A vertex job. -/
def vInfo : Com := .seq vDecode (.ite (.eq (V "cc") (V "cz")) vOwn vOther)

/-- Which colour pair and vertex combination slot `j` is for. -/
def cDecode : Com :=
  .seq (.assign "q" (sub (V "j") (V "nk")))
  (.seq (.assign "qn" (dvd (V "q") (V "n")))
  (.seq (.assign "z" (sub (V "q") (mul (V "qn") (V "n"))))
  (.seq (.assign "A" (dvd (V "qn") (V "k")))
  (.seq (.assign "Bc" (sub (V "qn") (mul (V "A") (V "k"))))
  (.seq (.assign "cz" (colOf "z"))
        (.assign "pz" (.get "r" (V "z"))))))))

/-- The slot's vertex has the smaller colour of the pair. -/
def cLow : Com :=
  .seq (.assign "rp" (sub (sub (mul (V "K") (V "pz")) (V "Bc")) (.lit 2)))
  (.seq (.assign "rd" (sub (sub (mul (V "K") (V "pz")) (V "Bc")) (.lit 1)))
  (.seq (.assign "Wt" (mul (V "c2") (V "pz")))
  (.seq (.assign "EL" (.lit 1)) (.assign "E1" (pairE (V "A") (V "Bc"))))))

/-- The slot's vertex has the larger colour of the pair. -/
def cHigh : Com :=
  .seq (.assign "rp" (add (add (mul (V "K") (sub (V "n") (V "pz"))) (V "A")) (.lit 2)))
  (.seq (.assign "rd" (add (mul (V "K") (V "n")) (.lit 2)))
  (.seq (.assign "Wt" (mul (V "c2") (sub (V "n") (V "pz"))))
  (.seq (.assign "EL" (.lit 1)) (.assign "E1" (pairE (V "A") (V "Bc"))))))

def cBody : Com :=
  .ite (.lt (V "A") (V "Bc"))
    (.ite (.eq (V "cz") (V "A")) cLow (.ite (.eq (V "cz") (V "Bc")) cHigh inert))
    inert

/-- A colour combination slot. -/
def cInfo : Com := .seq cDecode cBody

/-- The numbers of an edge job, once its endpoints are loaded. -/
def eTail : Com :=
  .seq (.assign "rp"
          (sub (add (sub (mul (V "K") (sub (V "pw") (V "pu"))) (V "cu")) (V "cw")) (.lit 1)))
  (.seq (.assign "rd" (sub (sub (mul (V "K") (V "pw")) (V "cu")) (.lit 1)))
  (.seq (.assign "Wt" (add (mul (V "c2") (sub (V "pw") (V "pu"))) (V "c3")))
  (.seq (.assign "EL" (.lit 1)) (.assign "E1" (pairE (V "cu") (V "cw"))))))

/-- The endpoints of edge job `j`, their ranks and their colours. -/
def eLoad : Com :=
  .seq (.assign "q" (sub (sub (V "j") (V "nk")) (V "nc")))
  (.seq (.assign "u" (.get "eu" (V "q")))
  (.seq (.assign "w" (.get "ev" (V "q")))
  (.seq (.assign "pu" (.get "r" (V "u")))
  (.seq (.assign "pw" (.get "r" (V "w")))
  (.seq (.assign "cu" (colOf "u"))
        (.assign "cw" (colOf "w")))))))

/-- An edge job. -/
def eInfo : Com := .seq eLoad eTail

/-- The clamp that makes `0 < p ≤ d` hold outright. -/
def clamp : Com :=
  .seq (.assign "P" (V "rp"))
  (.seq (.ite (.lt (V "rd") (V "P")) (.assign "P" (V "rd")) .skip)
  (.seq (.ite (.lt (V "P") (.lit 1)) (.assign "P" (.lit 1)) .skip)
  (.seq (.assign "D" (V "rd"))
        (.ite (.lt (V "D") (.lit 1)) (.assign "D" (.lit 1)) .skip))))

/-- Everything about job `j`. -/
def info : Com :=
  .seq (.ite (.lt (V "j") (V "nk")) vInfo
          (.ite (.lt (V "j") (V "nkc")) cInfo eInfo))
       clamp

/-! ### The passes -/

def procBody : Com := .seq info (.seq (.write (V "P")) (bump "j"))
def dueBody : Com := .seq info (.seq (.write (V "D")) (bump "j"))
def wtBody : Com := .seq info (.seq (.write (V "Wt")) (bump "j"))

def offBody : Com :=
  .seq (.write (V "o"))
  (.seq (.ite (.lt (V "j") (V "nJ"))
          (.seq info (.assign "o" (add (V "o") (V "EL")))) .skip)
        (bump "j"))

def tgtBody : Com :=
  .seq info
  (.seq (.ite (.lt (.lit 0) (V "EL")) (.write (V "E1")) .skip)
  (.seq (.ite (.lt (.lit 1) (V "EL")) (.write (V "E2")) .skip)
        (bump "j")))

def jobLoop (body : Com) (bound : String) : Com :=
  .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V bound)) body)

/-! ### The header -/

def header1 : Com :=
  .seq (.assign "K" (add (V "k") (.lit 2)))
  (.seq (.assign "c1" (add (V "n") (.lit 1)))
  (.seq (.assign "c2"
          (add (add (mul (mul (sub (V "k") (.lit 1)) (V "n")) (V "c1")) (V "n")) (.lit 1)))
        (.assign "val" (dvd (mul (V "k") (sub (V "k") (.lit 1))) (.lit 2)))))

def header2 : Com :=
  .seq (.assign "M" (add (V "val") (.lit 1)))
  (.seq (.assign "nc" (mul (mul (V "k") (V "k")) (V "n")))
  (.seq (.assign "nkc" (add (V "nk") (V "nc")))
  (.seq (.assign "nJ" (add (V "nkc") (V "E")))
        (.assign "N" (add (V "nJ") (.lit 1))))))

def header3 : Com :=
  .seq (.assign "W" (add (mul (mul (sub (V "k") (.lit 1)) (V "n")) (V "c1")) (V "k")))
    (.ite (.lt (.lit 1) (V "k"))
      (.seq (.assign "c3"
              (add (mul (mul (add (mul (V "k") (V "n")) (V "nc")) (V "n")) (V "c2"))
                (.lit 1)))
            (.assign "W"
              (add (add (mul (V "val") (V "c3")) (mul (V "val") (mul (V "n") (V "c2"))))
                (V "W"))))
      .skip)

def header : Com := .seq header1 (.seq header2 header3)

/-! ### The reduction -/

def setupA : Com :=
  .seq (.read "n") (.seq (.read "m")
  (.seq (.assign "L" (add (add (mul (.lit 2) (V "n")) (mul (.lit 2) (V "m"))) (.lit 2)))
        readLoop))

def setupB : Com :=
  .seq (.assign "tb" (add (V "n") (.lit 1)))
  (.seq (.assign "cb" (add (V "tb") (mul (.lit 2) (V "m"))))
  (.seq (.assign "k" (.get "a" (add (V "cb") (V "n"))))
  (.seq (.assign "nk" (mul (V "n") (V "k")))
  (.seq (.assign "cnt" (.lit 0)) rankLoop))))

def setupC : Com :=
  .seq (.assign "S" (add (V "n") (mul (.lit 2) (V "m"))))
  (.seq (.assign "u" (.lit 0)) (.seq (.assign "p" (.lit 0)) (.seq (.assign "E" (.lit 0))
        edgeLoop)))

def setup : Com := .seq setupA (.seq setupB (.seq setupC header))

def com : Com :=
  .seq setup
  (.seq (.write (V "nJ")) (.seq (.write (V "M"))
  (.seq (jobLoop procBody "nJ") (.seq (jobLoop dueBody "nJ") (.seq (jobLoop wtBody "nJ")
  (.seq (.assign "o" (.lit 0)) (.seq (jobLoop offBody "N") (.seq (jobLoop tgtBody "nJ")
    (.write (V "W"))))))))))

def layout : Layout :=
  ⟨["n", "m", "L", "t", "v", "tb", "cb", "k", "nk", "cnt", "i", "c", "u", "p", "w", "E",
    "S", "K", "c1", "c2", "c3", "val", "M", "nc", "nkc", "nJ", "N", "W", "j", "q", "qn",
    "z", "A", "Bc", "cz", "cc", "pz", "pu", "pw", "cu", "cw", "rp", "rd", "Wt", "EL",
    "E1", "E2", "P", "D", "o"], ["a", "r", "eu", "ev"], 8⟩

def prog : Lax808846.Ram.Program := compileProgram layout com

theorem com_ok : Com.Ok layout com := by
  simp [com, setup, setupA, setupB, setupC, vDecode, cDecode, cLow, cHigh, cBody, eLoad,
    header, header1, header2, header3, readLoop, readBody, rankLoop, rankBody, edgeLoop, edgeBody,
    jobLoop, procBody, dueBody, wtBody, offBody, tgtBody, info, clamp, vInfo, vOwn,
    vOther, cInfo, eInfo, eTail, inert, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by simp [Layout.const]

end Lax470956Proofs.Construction1Prog
