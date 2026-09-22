import Lax470956Proofs.Theorem2Assembly
import Lax470956Proofs.TMToNats
import Lax470956Proofs.TMToBits
import Lax470956Proofs.ParseRam
import Lax470956Proofs.PrintRam
import Lax470956.Theorem2

/-!
Theorem 2, from its four translations.
-/

namespace Lax470956Proofs.Theorem2

open Lax470956.NPHardness Lax470956.Scheduling
open Lax470956Proofs.Theorem2Assembly

/-- The four translations: bits to a word of bits and back, as Turing machines; the
parser and the printer, as word RAM programs. -/
noncomputable def parts : Parts where
  toNats := Lax470956Proofs.TMToNats.toNats
  toBits := Lax470956Proofs.TMToBits.toBits
  parse := Lax470956Proofs.ParseMain.parse
  parse_time := Lax470956Proofs.ParseRam.ramPolytime_parse
  parse_correct := fun w => by
    rw [Lax470956Proofs.ParseMain.parse, bitsOf_natBits]
    exact Lax470956Proofs.ParseSem.parseBits_correct w
  print := Lax470956Proofs.PrintModel.print
  print_time := Lax470956Proofs.PrintRam.ramPolytime_print
  print_correct := Lax470956Proofs.PrintModel.print_correct

/--
---
conclusion: Lax470956.Theorem2.npHardOn_allSchedulable_pmax_le
---
Tovey's theorem hands over a polynomial-time Turing reduction from any NP language to
exact `(3,4)`-SAT on bit-encoded formulas. The reduction to scheduling is its composite
with five machines: the bits become a word of zeros and ones; a word RAM program parses
that word — a one-pass scan of the rigid encoding, then a quadratic pass that renames each
variable to the position of its first occurrence and numbers its occurrences — into
Construction 2's formula word; Construction 2's own program turns the formula word into an
instance word; a second program prints the instance word in the binary instance encoding,
as a word of zeros and ones; and the last machine turns that word back into bits. The two
RAM programs are polynomial-time Turing computations by the archive's equivalence, and
the composite is polynomial by the composition theorem, taken here with the middle
alphabet general.

The image lies on the slice because Construction 2's instances do, and the composite
preserves and reflects yes-instances because the parser is correct against Tovey's
language, Construction 2 is correct, and the printer writes exactly the encoding of the
instance its word encodes.
-/
theorem npHardOn_allSchedulable_pmax_le :
    NPHardOn Instance.AllSchedulable fun I => I.pmax ≤ 25 ∧ ∀ j, I.w j = 1 :=
  npHardOn parts

/--
---
conclusion: Lax470956.Theorem2.npHard_allSchedulable
---
The slice statement, forgetting the slice.
-/
theorem npHard_allSchedulable : NPHard Instance.AllSchedulable := npHard parts

end Lax470956Proofs.Theorem2
