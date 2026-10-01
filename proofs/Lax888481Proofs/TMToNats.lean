import Lax888481Proofs.Theorem2Assembly
import Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram

set_option backward.isDefEq.respectTransparency false

/-!
From a binary word to the encoding of its bits, on a Turing machine.

A bit becomes a number, and a number is written as a separator followed by its binary
digits; so `true` becomes a separator and a one, and `false` a separator alone. The
machine pops the word off its input stack writing those symbols to a work stack, which
reverses them, and then moves the work stack to the output stack, which reverses them
back. Both loops are linear.
-/

namespace Lax888481Proofs.TMToNats

open Turing Lax759944.BinaryWordEncoding Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
open Lax888481Proofs.Theorem2Assembly

set_option genSizeOfSpec false in
/-- The three stacks. -/
inductive Key | inp | tmp | out
  deriving DecidableEq, Fintype

/-- The input is bits; the other two hold symbols. -/
def Γ : Key → Type
  | .inp => Bool
  | .tmp => Symbol
  | .out => Symbol

instance : Fintype (Γ .inp) := inferInstanceAs (Fintype Bool)

/-- Two registers: the bit and the symbol last popped. -/
abbrev Reg := Option Bool × Option Symbol

abbrev Prog := Program Γ Reg
abbrev St := Store Γ Reg

/-- A store, by its three stacks and its registers. -/
def st (i : List Bool) (t o : List Symbol) (r : Reg) : St where
  state := r
  stk := fun k => match k with
    | .inp => i
    | .tmp => t
    | .out => o

def rdI : Prog := .atom (.pop .inp (fun s b => (b, s.2)))
def rdT : Prog := .atom (.pop .tmp (fun s b => (s.1, b)))

def body1 : Prog :=
  .seq (.atom (.push .tmp (fun _ => Symbol.separator)))
    (.seq (.branch (fun s => s.1 == some true) (.atom (.push .tmp (fun _ => Symbol.one)))
        (.atom (.load id))) rdI)

abbrev loop1 : Prog := .loop (fun s => s.1.isSome) body1

def body2 : Prog := .seq (.atom (.push .out (fun s => s.2.getD Symbol.separator))) rdT

abbrev loop2 : Prog := .loop (fun s => s.2.isSome) body2

abbrev prog : Prog := .seq (.seq rdI loop1) (.seq rdT loop2)

/-- The symbols of one bit. -/
def enc (b : Bool) : List Symbol := if b then [.separator, .one] else [.separator]

lemma stk_ext {s t : St} (hs : s.state = t.state) (h : ∀ k, s.stk k = t.stk k) : s = t :=
  Store.ext _ _ hs (funext h)

lemma rdI_exec (i : List Bool) (t o : List Symbol) (r : Reg) :
    Executes rdI (st i t o r) (st i.tail t o (i.head?, r.2)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.pop .inp (fun s b => (b, s.2))) (st i t o r)
  have he : Op.apply (.pop .inp (fun (s : Reg) b => (b, s.2))) (st i t o r)
      = st i.tail t o (i.head?, r.2) := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma rdT_exec (i : List Bool) (t o : List Symbol) (r : Reg) :
    Executes rdT (st i t o r) (st i t.tail o (r.1, t.head?)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.pop .tmp (fun s b => (s.1, b))) (st i t o r)
  have he : Op.apply (.pop .tmp (fun (s : Reg) b => (s.1, b))) (st i t o r)
      = st i t.tail o (r.1, t.head?) := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma pushT_exec (i : List Bool) (t o : List Symbol) (r : Reg) (a : Symbol) :
    Executes (.atom (.push .tmp (fun _ => a))) (st i t o r) (st i (a :: t) o r) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.push .tmp (fun _ => a)) (st i t o r)
  have he : Op.apply (.push .tmp (fun (_ : Reg) => a)) (st i t o r) = st i (a :: t) o r := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma pushO_exec (i : List Bool) (t o : List Symbol) (r : Reg) :
    Executes (.atom (.push .out (fun s : Reg => s.2.getD Symbol.separator)))
      (st i t o r) (st i t (r.2.getD Symbol.separator :: o) r) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg)
    (.push .out (fun s : Reg => s.2.getD Symbol.separator)) (st i t o r)
  have he : Op.apply (.push .out (fun s : Reg => s.2.getD Symbol.separator)) (st i t o r)
      = st i t (r.2.getD Symbol.separator :: o) r := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

/-- The first loop writes the symbols of the word, reversed, onto the work stack. -/
lemma loop1_exec (bs : List Bool) (t o : List Symbol) (r2 : Option Symbol) :
    ∃ c ≤ 6 * bs.length + 1,
      Executes loop1 (st bs.tail t o (bs.head?, r2))
        (st [] ((bs.flatMap enc).reverse ++ t) o (none, r2)) c := by
  induction bs generalizing t with
  | nil => exact ⟨1, by simp, Executes.loop_false rfl⟩
  | cons b rest ih =>
      obtain ⟨c, hc, hrest⟩ := ih (t := (enc b).reverse ++ t)
      have hsep := pushT_exec rest t o (some b, r2) Symbol.separator
      cases b with
      | true =>
          have hone := pushT_exec rest (Symbol.separator :: t) o (some true, r2) Symbol.one
          have hrd := rdI_exec rest (Symbol.one :: Symbol.separator :: t) o (some true, r2)
          have hbody : Executes body1 (st rest t o (some true, r2))
              (st rest.tail (Symbol.one :: Symbol.separator :: t) o (rest.head?, r2)) _ :=
            .seq hsep (.seq (.branch_true (by rfl) hone) hrd)
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [enc] using hrest)⟩
          simp only [List.length_cons]; omega
      | false =>
          have hskip := Executes.atom (Γ := Γ) (σ := Reg) (.load id)
            (st rest (Symbol.separator :: t) o (some false, r2))
          have hrd := rdI_exec rest (Symbol.separator :: t) o (some false, r2)
          have hbody : Executes body1 (st rest t o (some false, r2))
              (st rest.tail (Symbol.separator :: t) o (rest.head?, r2)) _ :=
            .seq hsep (.seq (.branch_false (by rfl) hskip) hrd)
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [enc] using hrest)⟩
          simp only [List.length_cons]; omega

/-- The second loop moves the work stack to the output, reversing it again. -/
lemma loop2_exec (ts o : List Symbol) :
    ∃ c ≤ 3 * ts.length + 1,
      Executes loop2 (st [] ts.tail o (none, ts.head?)) (st [] [] (ts.reverse ++ o) (none, none)) c := by
  induction ts generalizing o with
  | nil => exact ⟨1, by simp, Executes.loop_false rfl⟩
  | cons a rest ih =>
      obtain ⟨c, hc, hrest⟩ := ih (o := a :: o)
      have hp := pushO_exec [] rest o (none, some a)
      have hrd := rdT_exec [] rest (a :: o) (none, some a)
      refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.2.isSome) rfl (.seq hp hrd)
        (by simpa using hrest)⟩
      simp only [List.length_cons]; omega

lemma enc_length (w : Word) : (w.flatMap enc).length ≤ 2 * w.length := by
  induction w with
  | nil => simp
  | cons b t ih => cases b <;> simp [enc] at ih ⊢ <;> omega

lemma encode_natBits (w : Word) : encode (natBits w) = w.flatMap enc := by
  induction w with
  | nil => rfl
  | cons b t ih =>
      simp only [natBits, List.map_cons, encode, List.flatMap_cons] at ih ⊢
      rw [ih]
      cases b <;> simp [enc, encodeNat]

lemma ioStore_inp (w : Word) : ioStore (Γ := Γ) Key.inp ((none, none) : Reg) w = st w [] [] (none, none) := by
  refine stk_ext rfl fun k => ?_
  cases k <;> simp [ioStore, st]

lemma ioStore_out (o : List Symbol) :
    ioStore (Γ := Γ) Key.out ((none, none) : Reg) o = st [] [] o (none, none) := by
  refine stk_ext rfl fun k => ?_
  cases k <;> simp [ioStore, st]

/-- **A binary word becomes the encoding of its bits in linear time.** -/
theorem toNats : Nonempty (TM2ComputableInPolyTime id encode natBits) := by
  refine program_polytime prog Key.inp Key.out ((none, none) : Reg) id encode natBits
    (Polynomial.C 18 * Polynomial.X + Polynomial.C 8) fun w => ?_
  obtain ⟨c1, hc1, h1⟩ := loop1_exec w [] [] none
  obtain ⟨c2, hc2, h2⟩ := loop2_exec ((w.flatMap enc).reverse ++ []) []
  have hr1 := rdI_exec w [] [] (none, none)
  have hr2 := rdT_exec [] ((w.flatMap enc).reverse ++ []) [] (none, none)
  have hlen := enc_length w
  refine ⟨1 + c1 + (1 + c2), ?_, ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      id]
    simp only [List.append_nil, List.length_reverse] at hc2
    omega
  · rw [ioStore_inp, ioStore_out, encode_natBits]
    have := Executes.seq (Executes.seq hr1 h1) (Executes.seq hr2 h2)
    simpa using this

end Lax888481Proofs.TMToNats
