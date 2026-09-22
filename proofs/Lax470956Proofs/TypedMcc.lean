import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

namespace Lax470956Proofs.TypedMcc

/-!
# Multicolored Clique

A `k`-partite graph, given as a finite vertex type with a coloring into `k` classes and a
symmetric edge relation holding only between differently-colored vertices. A multicolored
clique is a choice of one vertex per color, pairwise adjacent.

Parameterized by the number `k` of colors this problem is W[1]-hard
(Fellows–Hermelin–Rosamond–Vialette), which is the hardness that
`Proofs-ISEM/Theorem1_FromMulticoloredClique.lean` transports to interval scheduling.
-/

/-! ## 2. Multicolored Clique -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A graph for *Multicolored Clique*: a finite vertex type, a coloring into `k`
classes, and a symmetric edge relation. -/
structure MCCInstance (k : ℕ) where
  V : Type
  fintypeV : Fintype V
  decEqV : DecidableEq V
  color : V → Fin k
  E : V → V → Prop
  decE : DecidableRel E
  E_symm : ∀ u v, E u v → E v u

attribute [instance] MCCInstance.fintypeV MCCInstance.decEqV MCCInstance.decE

namespace MCCInstance

variable {k : ℕ} (G : MCCInstance k)

/-- `G` contains a multicolored clique of size `k`: one vertex per color, pairwise
adjacent across all distinct color pairs. -/
def HasClique : Prop :=
  ∃ f : Fin k → G.V, (∀ c, G.color (f c) = c) ∧ ∀ c c', c ≠ c' → G.E (f c) (f c')

end MCCInstance

end Lax470956Proofs.TypedMcc
