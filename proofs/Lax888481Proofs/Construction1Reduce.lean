import Lax888481Proofs.Construction1Emit
import Lax888481Proofs.Construction1Renum
import Lax888481Proofs.MccTransfer
import Lax888481Proofs.NoInstance

/-!
Construction 1 as a total map on words: the three combinatorial obligations of an
fpt-reduction.

A reduction is a function on all words, so the map has to say what it does with a word
that is not a graph. It sends it to a fixed instance with one job and no machine, which
cannot meet its threshold; so an unrecognized word is a no-instance, as it is for
Multicoloured Clique.

On a word that is a graph the map applies Construction 1 to the instance the word is
read as. Which instance that is, is a choice, and this file shows the choice does not
matter: a word determines its graph, its colouring and its number of colours, so
whichever instance is chosen has a multicoloured clique exactly when any other one does.

What is left of the reduction after this file is its running time, which is a program
rather than an argument.
-/

namespace Lax888481Proofs.Construction1Reduce

open Lax888481
open Lax888481.Scheduling Lax888481.InstanceEncoding
open Lax888481.Construction1
open Lax888481Proofs.EncodingTransfer Lax888481Proofs.MccTransfer

/-- The fixed no-instance word, with its instance and threshold. -/
theorem encodes_noWord :
    EncodesDecisionInstance Lax888481.Construction1.noWord NoInstance.noInst 1 :=
  NoInstance.encodes_decision

/-- On a word that is a graph, the map is Construction 1 applied to the instance chosen
for it. -/
theorem reduce_pos {x : List ℕ} (hx : ∃ G, MulticolouredClique.EncodesInstance x G) :
    reduce x = emit hx.choose := dif_pos hx

theorem reduce_neg {x : List ℕ} (hx : ¬ ∃ G, MulticolouredClique.EncodesInstance x G) :
    reduce x = Lax888481.Construction1.noWord := dif_neg hx

/--
---
conclusion: Lax888481.Construction1.reduce_maps
---
Either the map emits Construction 1's word, which presents the constructed instance and
its threshold, or it emits the fixed word, which presents one job and the threshold one.
-/
theorem reduce_maps (x : List ℕ) : reduce x ∈ DecisionInstances := by
  by_cases hx : ∃ G, MulticolouredClique.EncodesInstance x G
  · exact ⟨inst hx.choose, targetWeight hx.choose,
      (reduce_pos hx) ▸ Lax888481Proofs.Construction1Emit.emit_encodes hx.choose⟩
  · exact ⟨NoInstance.noInst, 1, (reduce_neg hx) ▸ encodes_noWord⟩

/--
---
conclusion: Lax888481.Construction1.reduce_correct
---
On a word that is a graph the claim is the correctness of Construction 1, transported
along the encoding on the right and along the choice of instance on the left; on any
other word both sides are false, the left because there is no graph and the right
because the word the map emits has a job it cannot run.
-/
theorem reduce_correct (x : List ℕ) :
    (∃ G, MulticolouredClique.EncodesInstance x G ∧ G.HasMulticolouredClique) ↔
      ∃ I W, EncodesDecisionInstance (reduce x) I W ∧ I.HasWeight W := by
  by_cases hx : ∃ G, MulticolouredClique.EncodesInstance x G
  · have hr := reduce_pos hx
    have hG₀ : MulticolouredClique.EncodesInstance x hx.choose := hx.choose_spec
    have henc := Lax888481Proofs.Construction1Emit.emit_encodes hx.choose
    rw [hr]
    constructor
    · rintro ⟨G, hG, hclq⟩
      exact ⟨inst hx.choose, targetWeight hx.choose, henc,
        (Lax888481Proofs.Construction1Renum.correct hx.choose).mp
          ((hasClique_congr hG hG₀).mp hclq)⟩
    · rintro ⟨I, W, hI, hw⟩
      exact ⟨hx.choose, hG₀, (Lax888481Proofs.Construction1Renum.correct hx.choose).mpr
        (hasWeight_dec hI henc hw)⟩
  · rw [reduce_neg hx]
    constructor
    · rintro ⟨G, hG, -⟩
      exact absurd ⟨G, hG⟩ hx
    · rintro ⟨I, W, hI, hw⟩
      exact absurd (hasWeight_dec hI encodes_noWord hw) NoInstance.not_hasWeight

/-- The second entry of Construction 1's word is its number of machines. -/
theorem machineCount_emit (G : MulticolouredClique.Instance) :
    machineCount (emit G) = nMach G := by
  simp [machineCount, Lax888481.Construction1.emit, List.getD]

/--
---
conclusion: Lax888481.Construction1.reduce_param
---
The constructed instance has one machine for each pair of colours and one more, and the
number of colours is the last entry of the word; so the parameter of the image is a
function of the parameter of the source alone. An unrecognized word is sent to a word
with no machine at all.
-/
theorem reduce_param (x : List ℕ) :
    machineCount (reduce x) ≤ (x.getLast?.getD 0).choose 2 + 1 := by
  by_cases hx : ∃ G, MulticolouredClique.EncodesInstance x G
  · rw [reduce_pos hx, machineCount_emit, param_eq hx.choose_spec]
    exact le_of_eq rfl
  · rw [reduce_neg hx]
    simp [machineCount, Lax888481.Construction1.noWord, List.getD]

end Lax888481Proofs.Construction1Reduce
