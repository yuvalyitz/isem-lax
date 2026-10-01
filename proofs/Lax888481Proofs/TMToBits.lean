import Lax888481Proofs.Theorem2Assembly
import Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram

set_option backward.isDefEq.respectTransparency false

/-!
From the encoding of a list of numbers to the binary word saying which are nonzero, on a
Turing machine.

A number is written as a separator followed by its binary digits, and zero has none; so a
number is nonzero exactly when a digit follows its separator. The machine reads the
symbols once, remembering for the number in progress whether a digit has been seen, and
writes that bit to a work stack when the next separator or the end of the input arrives.
A second loop moves the work stack to the output, restoring the order.
-/

namespace Lax888481Proofs.TMToBits

open Turing Lax759944.BinaryWordEncoding Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
open Lax888481Proofs.Theorem2Assembly

set_option genSizeOfSpec false in
inductive Key | inp | tmp | out
  deriving DecidableEq, Fintype

def Γ : Key → Type
  | .inp => Symbol
  | .tmp => Bool
  | .out => Bool

instance : Fintype (Γ .inp) := inferInstanceAs (Fintype Symbol)

/-- The symbol last read, the bit of the number in progress, and the bit last popped. -/
abbrev Reg := Option Symbol × Option Bool × Option Bool

abbrev Prog := Program Γ Reg
abbrev St := Store Γ Reg

def st (i : List Symbol) (t o : List Bool) (r : Reg) : St where
  state := r
  stk := fun k => match k with
    | .inp => i
    | .tmp => t
    | .out => o

lemma stk_ext {s t : St} (hs : s.state = t.state) (h : ∀ k, s.stk k = t.stk k) : s = t :=
  Store.ext _ _ hs (funext h)

abbrev rdI : Prog := .atom (.pop .inp (fun s b => (b, s.2.1, s.2.2)))
abbrev rdT : Prog := .atom (.pop .tmp (fun s b => (s.1, s.2.1, b)))
abbrev flush : Prog :=
  .branch (fun s => s.2.1.isSome) (.atom (.push .tmp (fun s => s.2.1.getD false)))
    (.atom (.load id))
abbrev setP (b : Option Bool) : Prog := .atom (.load (fun s => (s.1, b, s.2.2)))

abbrev body1 : Prog :=
  .seq (.branch (fun s => s.1 == some Symbol.separator) (.seq flush (setP (some false)))
      (setP (some true))) rdI

abbrev loop1 : Prog := .loop (fun s => s.1.isSome) body1
abbrev body2 : Prog := .seq (.atom (.push .out (fun s => s.2.2.getD false))) rdT
abbrev loop2 : Prog := .loop (fun s => s.2.2.isSome) body2
abbrev prog : Prog :=
  .seq (.seq rdI loop1) (.seq (.seq flush (setP none)) (.seq rdT loop2))

/-- The bits the first loop has pushed, in order, from pending bit `p` on symbols `l`. -/
def emitted : Option Bool → List Symbol → List Bool
  | _, [] => []
  | p, .separator :: r => p.toList ++ emitted (some false) r
  | _, _ :: r => emitted (some true) r

/-- The pending bit when the symbols run out. -/
def pendAfter : Option Bool → List Symbol → Option Bool
  | p, [] => p
  | _, .separator :: r => pendAfter (some false) r
  | _, _ :: r => pendAfter (some true) r

lemma rdI_exec (i : List Symbol) (t o : List Bool) (r : Reg) :
    Executes rdI (st i t o r) (st i.tail t o (i.head?, r.2.1, r.2.2)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.pop .inp (fun s b => (b, s.2.1, s.2.2)))
    (st i t o r)
  have he : Op.apply (.pop .inp (fun (s : Reg) b => (b, s.2.1, s.2.2))) (st i t o r)
      = st i.tail t o (i.head?, r.2.1, r.2.2) := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma rdT_exec (i : List Symbol) (t o : List Bool) (r : Reg) :
    Executes rdT (st i t o r) (st i t.tail o (r.1, r.2.1, t.head?)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.pop .tmp (fun s b => (s.1, s.2.1, b)))
    (st i t o r)
  have he : Op.apply (.pop .tmp (fun (s : Reg) b => (s.1, s.2.1, b))) (st i t o r)
      = st i t.tail o (r.1, r.2.1, t.head?) := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma setP_exec (i : List Symbol) (t o : List Bool) (r : Reg) (b : Option Bool) :
    Executes (setP b) (st i t o r) (st i t o (r.1, b, r.2.2)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.load (fun s => (s.1, b, s.2.2))) (st i t o r)
  exact h

/-- Flushing pushes the pending bit, if there is one. -/
lemma flush_exec (i : List Symbol) (t o : List Bool) (r : Reg) :
    Executes flush (st i t o r) (st i (r.2.1.toList.reverse ++ t) o r) 2 := by
  rcases hp : r.2.1 with _ | b
  · have h := Executes.atom (Γ := Γ) (σ := Reg) (.load id) (st i t o r)
    have he : Op.apply (.load id) (st i t o r) = st i t o r := rfl
    rw [he] at h
    have := Executes.branch_false (p := .atom (.push .tmp (fun s : Reg => s.2.1.getD false)))
      (b := fun s : Reg => s.2.1.isSome) (by simp [st, hp]) h
    simpa using this
  · have h := Executes.atom (Γ := Γ) (σ := Reg) (.push .tmp (fun s : Reg => s.2.1.getD false))
      (st i t o r)
    have he : Op.apply (.push .tmp (fun s : Reg => s.2.1.getD false)) (st i t o r)
        = st i (b :: t) o r := by
      refine stk_ext rfl fun k => ?_
      cases k <;> simp [Op.apply, st, hp]
    rw [he] at h
    have := Executes.branch_true (q := .atom (.load id))
      (b := fun s : Reg => s.2.1.isSome) (by simp [st, hp]) h
    simpa using this

lemma pushO_exec (i : List Symbol) (t o : List Bool) (r : Reg) :
    Executes (.atom (.push .out (fun s : Reg => s.2.2.getD false)))
      (st i t o r) (st i t (r.2.2.getD false :: o) r) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg)
    (.push .out (fun s : Reg => s.2.2.getD false)) (st i t o r)
  have he : Op.apply (.push .out (fun s : Reg => s.2.2.getD false)) (st i t o r)
      = st i t (r.2.2.getD false :: o) r := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma loop1_exec (l : List Symbol) (p : Option Bool) (t o : List Bool) (r3 : Option Bool) :
    ∃ c ≤ 6 * l.length + 1,
      Executes loop1 (st l.tail t o (l.head?, p, r3))
        (st [] ((emitted p l).reverse ++ t) o (none, pendAfter p l, r3)) c := by
  induction l generalizing p t with
  | nil => exact ⟨1, by simp, by simpa [emitted, pendAfter] using Executes.loop_false rfl⟩
  | cons a rest ih =>
      cases a with
      | separator =>
          obtain ⟨c, hc, hrest⟩ := ih (p := some false) (t := p.toList.reverse ++ t)
          have hf := flush_exec rest t o (some Symbol.separator, p, r3)
          have hs := setP_exec rest (p.toList.reverse ++ t) o (some Symbol.separator, p, r3)
            (some false)
          have hrd := rdI_exec rest (p.toList.reverse ++ t) o
            (some Symbol.separator, some false, r3)
          have hbody : Executes body1 (st rest t o (some Symbol.separator, p, r3))
              (st rest.tail (p.toList.reverse ++ t) o (rest.head?, some false, r3)) _ :=
            .seq (.branch_true (by rfl) (.seq hf hs)) hrd
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [emitted, pendAfter] using hrest)⟩
          simp only [List.length_cons]; omega
      | zero =>
          obtain ⟨c, hc, hrest⟩ := ih (p := some true) (t := t)
          have hs := setP_exec rest t o (some Symbol.zero, p, r3) (some true)
          have hrd := rdI_exec rest t o (some Symbol.zero, some true, r3)
          have hbody : Executes body1 (st rest t o (some Symbol.zero, p, r3))
              (st rest.tail t o (rest.head?, some true, r3)) _ :=
            .seq (.branch_false (by rfl) hs) hrd
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [emitted, pendAfter] using hrest)⟩
          simp only [List.length_cons]; omega
      | one =>
          obtain ⟨c, hc, hrest⟩ := ih (p := some true) (t := t)
          have hs := setP_exec rest t o (some Symbol.one, p, r3) (some true)
          have hrd := rdI_exec rest t o (some Symbol.one, some true, r3)
          have hbody : Executes body1 (st rest t o (some Symbol.one, p, r3))
              (st rest.tail t o (rest.head?, some true, r3)) _ :=
            .seq (.branch_false (by rfl) hs) hrd
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [emitted, pendAfter] using hrest)⟩
          simp only [List.length_cons]; omega

lemma loop2_exec (ts o : List Bool) :
    ∃ c ≤ 3 * ts.length + 1,
      Executes loop2 (st [] ts.tail o (none, none, ts.head?))
        (st [] [] (ts.reverse ++ o) (none, none, none)) c := by
  induction ts generalizing o with
  | nil => exact ⟨1, by simp, Executes.loop_false rfl⟩
  | cons a rest ih =>
      obtain ⟨c, hc, hrest⟩ := ih (o := a :: o)
      have hp := pushO_exec [] rest o (none, none, some a)
      have hrd := rdT_exec [] rest (a :: o) (none, none, some a)
      refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.2.2.isSome) rfl (.seq hp hrd)
        (by simpa using hrest)⟩
      simp only [List.length_cons]; omega

/-! ### What the Loop Computes -/

/-- Everything the machine writes: the bits pushed, then the pending one. -/
def total (p : Option Bool) (l : List Symbol) : List Bool :=
  emitted p l ++ (pendAfter p l).toList

lemma total_sep (p : Option Bool) (r : List Symbol) :
    total p (Symbol.separator :: r) = p.toList ++ total (some false) r := by
  simp [total, emitted, pendAfter]

lemma total_digits (p : Option Bool) (ds r : List Symbol)
    (hds : ∀ s ∈ ds, s ≠ Symbol.separator) :
    total p (ds ++ r) = total (if ds = [] then p else some true) r := by
  induction ds generalizing p with
  | nil => simp
  | cons a ds ih =>
      have ha : a ≠ Symbol.separator := hds a (by simp)
      have hstep : total p (a :: (ds ++ r)) = total (some true) (ds ++ r) := by
        cases a <;> simp_all [total, emitted, pendAfter]
      rw [List.cons_append, hstep, ih _ (fun s hs => hds s (by simp [hs]))]
      by_cases h : ds = [] <;> simp [h]

lemma bits_eq_nil_iff (n : ℕ) : n.bits = [] ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    have h1 : n.bits.length = n.size := Nat.size_eq_bits_len n
    have h2 : 0 < n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [h] at h1; simp at h1; omega
  · rintro rfl; simp

lemma total_encodeNat (p : Option Bool) (n : ℕ) (r : List Symbol) :
    total p (encodeNat n ++ r) = p.toList ++ total (some (decide (n ≠ 0))) r := by
  rw [encodeNat, List.cons_append, total_sep, total_digits _ _ _ (by
    intro s hs
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
    cases b <;> simp)]
  congr 2
  by_cases hn : n = 0
  · subst hn; simp
  · have : n.bits ≠ [] := fun h => hn ((bits_eq_nil_iff n).mp h)
    simp [this, hn]

lemma total_encode (p : Option Bool) (l : List ℕ) :
    total p (encode l) = p.toList ++ bitsOf l := by
  induction l generalizing p with
  | nil => simp [total, encode, emitted, pendAfter, bitsOf]
  | cons n l ih =>
      rw [show encode (n :: l) = encodeNat n ++ encode l by simp [encode], total_encodeNat, ih]
      simp [bitsOf]

lemma ioStore_inp (w : List Symbol) :
    ioStore (Γ := Γ) Key.inp ((none, none, none) : Reg) w = st w [] [] (none, none, none) := by
  refine stk_ext rfl fun k => ?_
  cases k <;> simp [ioStore, st]

lemma ioStore_out (o : List Bool) :
    ioStore (Γ := Γ) Key.out ((none, none, none) : Reg) o = st [] [] o (none, none, none) := by
  refine stk_ext rfl fun k => ?_
  cases k <;> simp [ioStore, st]

lemma emitted_length (p : Option Bool) (l : List Symbol) :
    (emitted p l).length + (pendAfter p l).toList.length ≤ l.length + 1 := by
  induction l generalizing p with
  | nil => cases p <;> simp [emitted, pendAfter]
  | cons a r ih =>
      cases a
      · have := ih (some false)
        cases p <;> simp [emitted, pendAfter] at this ⊢ <;> omega
      · have := ih (some true); simp [emitted, pendAfter] at this ⊢; omega
      · have := ih (some true); simp [emitted, pendAfter] at this ⊢; omega

/-- **The encoding of a list of numbers becomes its word of nonzero flags in linear
time.** -/
theorem toBits : Nonempty (TM2ComputableInPolyTime encode id bitsOf) := by
  refine program_polytime prog Key.inp Key.out ((none, none, none) : Reg) encode id bitsOf
    (Polynomial.C 12 * Polynomial.X + Polynomial.C 12) fun l => ?_
  set w := encode l with hw
  obtain ⟨c1, hc1, h1⟩ := loop1_exec w none [] [] none
  have hr1 := rdI_exec w [] [] (none, none, none)
  have hf := flush_exec [] ((emitted none w).reverse ++ []) [] (none, pendAfter none w, none)
  have hs := setP_exec [] ((pendAfter none w).toList.reverse ++ ((emitted none w).reverse ++ []))
    [] (none, pendAfter none w, none) none
  have htot : (pendAfter none w).toList.reverse ++ ((emitted none w).reverse ++ [])
      = (bitsOf l).reverse := by
    have := total_encode none l
    simp only [total, Option.toList_none, List.nil_append] at this
    rw [← this, ← hw]; simp
  rw [htot] at hs hf
  obtain ⟨c2, hc2, h2⟩ := loop2_exec (bitsOf l).reverse []
  have hr2 := rdT_exec [] (bitsOf l).reverse [] (none, none, none)
  have hlen := emitted_length none w
  have hbl : (bitsOf l).length ≤ w.length + 1 := by
    have := congrArg List.length htot
    simp at this; omega
  refine ⟨1 + c1 + (2 + 1 + (1 + c2)), ?_, ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simp only [List.length_reverse] at hc2
    omega
  · rw [ioStore_inp, ioStore_out]
    have := Executes.seq (Executes.seq hr1 h1) (Executes.seq (Executes.seq hf hs)
      (Executes.seq hr2 h2))
    simpa using this

end Lax888481Proofs.TMToBits
