import Lax470956Proofs.Theorem2Assembly

/-!
The printer, as a function: from an instance word to the bits of the instance's binary
encoding.
-/

namespace Lax470956Proofs.PrintModel

open Lax470956.Scheduling Lax470956.InstanceEncoding Lax470956.BinaryEncoding
open Lax470956Proofs.Theorem2Assembly

/-- The `i`-th binary digit of `n`. -/
def digit (n i : ℕ) : ℕ := n / 2 ^ i % 2

/-- The self-delimiting code of a number, as zeros and ones: its length in unary, a
zero, its digits. -/
def bitsNat (n : ℕ) : List ℕ :=
  List.replicate n.size 1 ++ [0] ++ (List.range n.size).map (digit n)

lemma bits_eq_digits (n : ℕ) :
    n.bits.map (fun b => if b then 1 else 0) = (List.range n.size).map (digit n) := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
      by_cases hz : Nat.bit b n = 0
      · rw [hz]; simp
      · rw [Nat.bits_append_bit n b h, Nat.size_bit hz, List.range_succ_eq_map, List.map_cons,
          List.map_cons, List.map_map, ih]
        congr 1
        · cases b <;> simp [digit, Nat.bit_val]
        · refine List.map_congr_left fun i _ => ?_
          simp only [Function.comp, digit, pow_succ]
          rw [Nat.mul_comm, ← Nat.div_div_eq_div_mul]
          congr 2
          cases b <;> simp [Nat.bit_val] <;> omega

lemma natBits_encodeNat (n : ℕ) : natBits (encodeNat n) = bitsNat n := by
  simp only [natBits, encodeNat, bitsNat, List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [bits_eq_digits, Nat.size_eq_bits_len]
  simp

/-! ### The Printer -/

/-- The word is long enough for the job and machine counts it declares. Every loop of the
printer is bounded by one of the two, so it stays polynomial on a word that
is not an instance at all. -/
def Guard (y : List ℕ) : Prop := 3 + 4 * jobCount y ≤ y.length ∧ machineCount y ≤ y.length

instance (y : List ℕ) : Decidable (Guard y) := inferInstanceAs (Decidable (_ ∧ _))

/-- The number of target entries the word has room for. -/
def room (y : List ℕ) : ℕ := y.length - (3 + 4 * jobCount y)

open Classical in
/-- Whether machine `i` appears in the block of job `j`, the block clipped to the word. -/
noncomputable def eligBit (y : List ℕ) (j i : ℕ) : ℕ :=
  if ∃ t, min (offset y j) (room y) ≤ t ∧ t < min (offset y (j + 1)) (room y) ∧ target y t = i
  then 1 else 0

/-- **The printer.** -/
noncomputable def print (y : List ℕ) : List ℕ :=
  if Guard y then
    bitsNat (jobCount y) ++ bitsNat (machineCount y) ++
      (List.range (jobCount y)).flatMap (fun j => bitsNat (proc y j)) ++
      (List.range (jobCount y)).flatMap (fun j => bitsNat (due y j)) ++
      (List.range (jobCount y)).flatMap (fun j => bitsNat (wt y j)) ++
      (List.range (jobCount y)).flatMap
        (fun j => (List.range (machineCount y)).map (eligBit y j))
  else []

lemma fin_val_range (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

lemma flatMap_fin {α : Type} (n : ℕ) (g : ℕ → List α) :
    (List.finRange n).flatMap (fun j => g j.val) = (List.range n).flatMap g := by
  rw [← fin_val_range, List.flatMap_map]

lemma map_fin {α : Type} (n : ℕ) (g : ℕ → α) :
    (List.finRange n).map (fun i => g i.val) = (List.range n).map g := by
  rw [← fin_val_range, List.map_map]; rfl

lemma natBits_append (a b : List Bool) : natBits (a ++ b) = natBits a ++ natBits b := by
  simp [natBits]

lemma natBits_flatMap {α : Type} (l : List α) (g : α → List Bool) :
    natBits (l.flatMap g) = l.flatMap fun a => natBits (g a) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, natBits_append, ih]

/-- The offsets of an instance word never exceed the last one. -/
lemma offset_le_last {y : List ℕ} {I : Instance} (h : EncodesInstance y I) :
    ∀ j ≤ I.jobs, offset y j ≤ offset y I.jobs := by
  have hmono : ∀ k ≤ I.jobs, ∀ j ≤ k, offset y j ≤ offset y k := by
    intro k
    induction k with
    | zero => intro _ j hj; have : j = 0 := by omega
              subst this; exact le_refl _
    | succ p ih =>
        intro hp j hj
        rcases Nat.lt_or_ge j (p + 1) with hlt | hge
        · exact le_trans (ih (by omega) j (by omega)) (h.offset_mono p (by omega))
        · have : j = p + 1 := by omega
          subst this; exact le_refl _
  exact fun j hj => hmono I.jobs (le_refl _) j hj

/-- **On an instance word the printer writes the instance's binary encoding.** -/
theorem print_correct (y : List ℕ) (I : Instance) (h : EncodesInstance y I)
    (hm : I.machines ≤ y.length) : print y = natBits (encodeInstance I) := by
  have hJ := h.jobCount_eq
  have hM := h.machineCount_eq
  have hlen := h.length_eq
  have hg : Guard y := ⟨by rw [hJ]; omega, by rw [hM]; exact hm⟩
  have hroom : room y = offset y I.jobs := by rw [room, hJ]; omega
  rw [print, if_pos hg, encodeInstance]
  simp only [natBits_append, natBits_flatMap, natBits_encodeNat, hJ, hM]
  have e1 : (List.finRange I.jobs).flatMap (fun j => bitsNat (I.p j))
      = (List.range I.jobs).flatMap (fun j => bitsNat (proc y j)) := by
    rw [← flatMap_fin I.jobs fun j => bitsNat (proc y j)]
    exact List.flatMap_congr fun j _ => by rw [h.proc_eq j]
  have e2 : (List.finRange I.jobs).flatMap (fun j => bitsNat (I.d j))
      = (List.range I.jobs).flatMap (fun j => bitsNat (due y j)) := by
    rw [← flatMap_fin I.jobs fun j => bitsNat (due y j)]
    exact List.flatMap_congr fun j _ => by rw [h.due_eq j]
  have e3 : (List.finRange I.jobs).flatMap (fun j => bitsNat (I.w j))
      = (List.range I.jobs).flatMap (fun j => bitsNat (wt y j)) := by
    rw [← flatMap_fin I.jobs fun j => bitsNat (wt y j)]
    exact List.flatMap_congr fun j _ => by rw [h.wt_eq j]
  have e4 : (List.finRange I.jobs).flatMap (fun j => natBits
        ((List.finRange I.machines).map fun i => decide (i ∈ I.eligible j)))
      = (List.range I.jobs).flatMap
        (fun j => (List.range I.machines).map (eligBit y j)) := by
    rw [← flatMap_fin I.jobs fun j => (List.range I.machines).map (eligBit y j)]
    refine List.flatMap_congr fun j _ => ?_
    rw [← map_fin I.machines (eligBit y j), natBits, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    have h1 := offset_le_last h j (by omega)
    have h2 := offset_le_last h (j + 1) (by omega)
    have hiff : (∃ t, min (offset y j) (room y) ≤ t ∧ t < min (offset y (j + 1)) (room y) ∧
        target y t = i) ↔ i ∈ I.eligible j := by
      rw [hroom, Nat.min_eq_left h1, Nat.min_eq_left h2]
      exact (h.eligible_iff j i).symm
    simp only [Function.comp, eligBit]
    by_cases hmem : i ∈ I.eligible j
    · rw [if_pos (hiff.mpr hmem)]; simp [hmem]
    · rw [if_neg (fun hex => hmem (hiff.mp hex))]; simp [hmem]
  rw [e1, e2, e3, e4]

end Lax470956Proofs.PrintModel
