import Lax888481Proofs.Checker
import Lax888481Proofs.TMCompose
import Lax888481.Theorem2
import Lax888481.SatVariant
import Lax759944Proofs.TuringRamPolytimeEquivalence

/-!
Theorem 2, assembled from its parts.

NP-hardness is a statement about Turing machines reading binary words, and Construction 2
is a word RAM program reading numbers. Between the two stand four translations: a binary
word has to become a list of numbers the word RAM can be handed, the bit-encoded formula
has to become the nine-numbers-per-clause word Construction 2 reads, the instance word it
writes has to become the binary encoding of the instance, and that list of bits has to
become a binary word again. This file says exactly what each of the four has to satisfy
and proves the theorem from them; the files that follow discharge them one at a time.
-/

namespace Lax888481Proofs.Theorem2Assembly

open Turing Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944.TuringPolytime
open Lax888481.Scheduling Lax888481.InstanceEncoding Lax888481.BinaryEncoding
open Lax888481.NPHardness Lax888481.SatVariant

/-- A binary word as a list of zeros and ones. -/
def natBits (w : Word) : List ℕ := w.map fun b => if b then 1 else 0

/-- A list of numbers as a binary word: which entries are nonzero. -/
def bitsOf (l : List ℕ) : Word := l.map fun n => decide (n ≠ 0)

@[simp] lemma bitsOf_natBits (w : Word) : bitsOf (natBits w) = w := by
  induction w with
  | nil => rfl
  | cons b t ih =>
      simp only [natBits, bitsOf, List.map_cons, List.map_map] at ih ⊢
      rw [ih]; cases b <;> simp

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- **The four translations Theorem 2 needs.** -/
structure Parts where
  /-- A binary word, handed to a Turing machine, becomes the encoding of its bits. -/
  toNats : Nonempty (TM2ComputableInPolyTime id encode natBits)
  /-- And back. -/
  toBits : Nonempty (TM2ComputableInPolyTime encode id bitsOf)
  /-- The parser: from a bit-encoded formula to Construction 2's word. -/
  parse : List ℕ → List ℕ
  parse_time : RamPolytime parse
  parse_correct : ∀ w : Word,
    w ∈ SAT34 ↔ parse (natBits w) ∈ Lax888481.Exact34Encoding.Satisfiable
  /-- The printer: from an instance word to the bits of the instance's binary encoding. -/
  print : List ℕ → List ℕ
  print_time : RamPolytime print
  print_correct : ∀ (y : List ℕ) (I : Instance), EncodesInstance y I →
    I.machines ≤ y.length → print y = natBits (encodeInstance I)

/-- A polynomial-time word RAM computation is a polynomial-time Turing computation. -/
lemma turing_of_ram {f : List ℕ → List ℕ} (h : RamPolytime f) :
    Nonempty (TM2ComputableInPolyTime encode encode f) :=
  (Lax759944Proofs.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime f).mp h

variable (P : Parts)

open Classical in
/-- The instance a binary word is sent to. -/
noncomputable def instOf (w : Word) : Instance :=
  (Lax888481Proofs.Reduce.reduce_slice (P.parse (natBits w))).choose

lemma instOf_spec (w : Word) :
    EncodesInstance (Lax888481.Construction2.reduce (P.parse (natBits w))) (instOf P w) ∧
      (instOf P w).pmax ≤ 25 ∧ ∀ j, (instOf P w).w j = 1 :=
  (Lax888481Proofs.Reduce.reduce_slice (P.parse (natBits w))).choose_spec

/-- The word is a satisfiable exact `(3,4)` formula exactly when its instance can schedule
every job. -/
lemma instOf_correct (w : Word) : w ∈ SAT34 ↔ (instOf P w).AllSchedulable := by
  rw [P.parse_correct, Lax888481Proofs.Reduce.reduce_correct]
  constructor
  · rintro ⟨I, hI, hall⟩
    exact Lax888481Proofs.EncodingTransfer.allSchedulable_imp hI (instOf_spec P w).1 hall
  · exact fun h => ⟨_, (instOf_spec P w).1, h⟩

/-- Construction 2 never declares more machines than its word is long. -/
lemma machines_le_length (z : List ℕ) :
    machineCount (Lax888481.Construction2.reduce z) ≤ (Lax888481.Construction2.reduce z).length := by
  classical
  unfold Lax888481.Construction2.reduce
  split_ifs
  · simp [machineCount, Lax888481.Construction2.emit, Lax888481.Construction2.procBlock,
      Lax888481.Construction2.dueBlock, Lax888481.Construction2.wtBlock,
      Lax888481.Construction2.offBlock, Lax888481.Construction2.nMach,
      Lax888481.Construction2.nJobs]
    omega
  · simp [machineCount, Lax888481.Construction2.noWord]

/-- The whole translation, as a function on binary words. -/
lemma chain_eq (w : Word) :
    bitsOf (P.print (Lax888481.Construction2.reduce (P.parse (natBits w))))
      = encodeInstance (instOf P w) := by
  have h := (instOf_spec P w).1
  rw [P.print_correct _ _ h (by rw [← h.machineCount_eq]; exact machines_le_length _),
    bitsOf_natBits]

/-- **The translation is polynomial-time on a Turing machine.** -/
theorem instOf_polytime : Nonempty (TM2ComputableInPolyTime id encodeInstance (instOf P)) := by
  obtain ⟨t1⟩ := P.toNats
  obtain ⟨t2⟩ := turing_of_ram P.parse_time
  obtain ⟨t3⟩ := turing_of_ram Lax888481Proofs.Checker.reduce_ramPolytime
  obtain ⟨t4⟩ := turing_of_ram P.print_time
  obtain ⟨t5⟩ := P.toBits
  obtain ⟨c12⟩ := Lax888481Proofs.TMCompose.comp t1 t2
  obtain ⟨c123⟩ := Lax888481Proofs.TMCompose.comp c12 t3
  obtain ⟨c1234⟩ := Lax888481Proofs.TMCompose.comp c123 t4
  obtain ⟨c⟩ := Lax888481Proofs.TMCompose.comp c1234 t5
  refine ⟨{ tm := c.tm, inputAlphabet := c.inputAlphabet, outputAlphabet := c.outputAlphabet,
            time := c.time, outputsFun := fun w => ?_ }⟩
  have h := c.outputsFun w
  simp only [Function.comp_apply, chain_eq] at h
  exact h

/-- Both forms of the theorem at once. -/
theorem npHardOn (P : Parts) :
    NPHardOn Instance.AllSchedulable fun I => I.pmax ≤ 25 ∧ ∀ j, I.w j = 1 := by
  intro A hA
  obtain ⟨g, ⟨tg⟩, hg⟩ := sat34_npHard A hA
  obtain ⟨t⟩ := instOf_polytime P
  obtain ⟨c⟩ := Lax434930Proofs.PolynomialComposition.comp tg t
  exact ⟨instOf P ∘ g, ⟨c⟩, fun x =>
    ⟨(instOf_spec P (g x)).2, (hg x).trans (instOf_correct P (g x))⟩⟩

theorem npHard (P : Parts) : NPHard Instance.AllSchedulable := fun A hA => by
  obtain ⟨f, hf, h⟩ := npHardOn P A hA
  exact ⟨f, hf, fun x => (h x).2⟩

end Lax888481Proofs.Theorem2Assembly
