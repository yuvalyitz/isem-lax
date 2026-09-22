import Lax470956Proofs.Theorem2Assembly

/-!
The parser, as a function: a finite-state scan of the bits of a formula's encoding.

Exact `(3,4)` formulas have a rigid encoding — every clause is three literals — so one
left-to-right pass with a five-valued phase recognises them, one bit a step. The scan is
the model the RAM program is proved against; what it accepts is settled here, without a
program in sight: the bits it has consumed are always recoverable from its state, so an
accepting scan has read exactly the encoding of the clauses it collected.
-/

namespace Lax470956Proofs.ParseModel

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The state of the scan: the phase, the unary counter, the clauses completed, and the
literals of the clause being read. -/
structure St where
  ph : ℕ
  n : ℕ
  done : List Clause
  cur : Clause

def init : St := ⟨0, 0, [], []⟩

/-- One bit. Phases: `0` between clauses, `1` between literals, `2` in a variable index,
`3` at a sign, `4` finished, `5` rejected. -/
def step (s : St) (b : Bool) : St :=
  match s.ph with
  | 0 => if b then { s with ph := 1 } else { s with ph := 4 }
  | 1 =>
      if s.cur.length < 3 then (if b then { s with ph := 2, n := 0 } else { s with ph := 5 })
      else (if b then { s with ph := 5 } else ⟨0, s.n, s.done ++ [s.cur], []⟩)
  | 2 => if b then { s with n := s.n + 1 } else { s with ph := 3 }
  | 3 => ⟨1, s.n, s.done, s.cur ++ [⟨s.n, b⟩]⟩
  | _ => { s with ph := 5 }

def run (s : St) (w : Word) : St := w.foldl step s

@[simp] def run_nil (s : St) : run s [] = s := rfl
@[simp] lemma run_cons (s : St) (b : Bool) (w : Word) : run s (b :: w) = run (step s b) w := rfl
lemma run_append (s : St) (u v : Word) : run s (u ++ v) = run (run s u) v := by
  simp [run, List.foldl_append]

/-! ### What an accepting scan has read -/

lemma encodeList_eq {α : Type} (e : α → Word) (l : List α) :
    encodeList e l = l.flatMap (fun a => true :: e a) ++ [false] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [encodeList, ih]

def curBits (c : Clause) : Word := c.flatMap fun l => true :: encodeLiteral l

def doneBits (d : List Clause) : Word := d.flatMap fun c => true :: encodeClause c

/-- The bits consumed so far, read back off the state. -/
def consumed (s : St) : Word :=
  match s.ph with
  | 0 => doneBits s.done
  | 1 => doneBits s.done ++ true :: curBits s.cur
  | 2 => doneBits s.done ++ true :: curBits s.cur ++ true :: List.replicate s.n true
  | 3 => doneBits s.done ++ true :: curBits s.cur ++ true :: List.replicate s.n true ++ [false]
  | 4 => doneBits s.done ++ [false]
  | _ => []

abbrev Good (s : St) : Prop :=
  (∀ c ∈ s.done, c.length = 3) ∧ s.cur.length ≤ 3 ∧ (s.ph = 0 ∨ s.ph = 4 → s.cur = []) ∧
    (s.ph = 2 ∨ s.ph = 3 → s.cur.length < 3)

lemma step_alive {s : St} {b : Bool} (h : (step s b).ph ≤ 4) : s.ph ≤ 3 := by
  by_contra hc
  have : 4 ≤ s.ph := by omega
  obtain ⟨ph, n, d, c⟩ := s
  simp only at this
  match ph, this with
  | k + 4, _ => simp [step] at h

lemma step_inv {s : St} {b : Bool} (hg : Good s) (h : (step s b).ph ≤ 4) :
    Good (step s b) ∧ consumed (step s b) = consumed s ++ [b] := by
  have hph := step_alive h
  obtain ⟨ph, n, d, c⟩ := s
  obtain ⟨h1, h2, h3, h4⟩ := hg
  simp only at h1 h2 h3 h4 hph
  have hcases : ph = 0 ∨ ph = 1 ∨ ph = 2 ∨ ph = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hc : c = [] := h3 (Or.inl rfl)
    subst hc
    cases b
    · exact ⟨⟨h1, by simp [step], by simp [step], by simp [step]⟩, by simp [step, consumed]⟩
    · exact ⟨⟨h1, by simp [step], by simp [step], by simp [step]⟩,
        by simp [step, consumed, curBits]⟩
  · by_cases hl : c.length < 3
    · cases b
      · simp [step, hl] at h
      · exact ⟨⟨by simpa [step, hl] using h1, by simpa [step, hl] using h2, by simp [step, hl],
          by simpa [step, hl] using hl⟩, by simp [step, hl, consumed]⟩
    · cases b
      · have hc3 : c.length = 3 := by omega
        refine ⟨⟨?_, by simp [step, hl], by simp [step, hl], by simp [step, hl]⟩, ?_⟩
        · intro c' hc'
          have hc'' : c' ∈ d ∨ c' = c := by simpa [step, hl] using hc'
          rcases hc'' with hc'' | rfl
          · exact h1 _ hc''
          · exact hc3
        · simp [step, hl, consumed, doneBits, encodeClause, encodeList_eq, curBits]
      · simp [step, hl] at h
  · have hl := h4 (Or.inl rfl)
    cases b
    · exact ⟨⟨h1, h2, by simp [step], by simpa [step] using hl⟩, by simp [step, consumed]⟩
    · refine ⟨⟨h1, h2, by simp [step], by simpa [step] using hl⟩, ?_⟩
      simp [step, consumed, List.replicate_succ']
  · have hl := h4 (Or.inr rfl)
    refine ⟨⟨h1, by simp [step]; omega, by simp [step], by simp [step]⟩, ?_⟩
    simp [step, consumed, curBits, encodeLiteral, encodeNat]

lemma run_inv (w : Word) (h : (run init w).ph ≤ 4) :
    Good (run init w) ∧ consumed (run init w) = w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨⟨by simp [init], by simp [init], by simp [init], by simp [init]⟩, rfl⟩
  | append_singleton u b ih =>
      rw [run_append] at h ⊢
      simp only [run_cons, run_nil] at h ⊢
      have ih' := ih (by have := step_alive h; omega)
      obtain ⟨hg, hc⟩ := step_inv ih'.1 h
      exact ⟨hg, by rw [hc, ih'.2]⟩

/-- **Soundness of the scan**: if it accepts, the word is the encoding of the clauses it
collected, and each of them has three literals. -/
theorem accept_sound {w : Word} (h : (run init w).ph = 4) :
    encodeCNF (run init w).done = w ∧ ∀ c ∈ (run init w).done, c.length = 3 := by
  obtain ⟨hg, hc⟩ := run_inv w (by omega)
  refine ⟨?_, hg.1⟩
  have : consumed (run init w) = encodeCNF (run init w).done := by
    simp [consumed, h, encodeCNF, encodeList_eq, doneBits]
  rw [← this, hc]

/-! ### What the scan accepts -/

lemma run_ones (n0 m : ℕ) (d : List Clause) (c : Clause) (w : Word) :
    run ⟨2, n0, d, c⟩ (List.replicate m true ++ w) = run ⟨2, n0 + m, d, c⟩ w := by
  induction m generalizing n0 with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ, List.cons_append, run_cons]
      have : step ⟨2, n0, d, c⟩ true = ⟨2, n0 + 1, d, c⟩ := by simp [step]
      rw [this, ih]; congr 2; omega

lemma run_lit (n0 : ℕ) (d : List Clause) (c : Clause) (hc : c.length < 3) (l : Literal)
    (w : Word) :
    run ⟨1, n0, d, c⟩ (true :: encodeLiteral l ++ w) = run ⟨1, l.index, d, c ++ [l]⟩ w := by
  have h1 : step ⟨1, n0, d, c⟩ true = ⟨2, 0, d, c⟩ := by simp [step, hc]
  rw [List.cons_append, run_cons, h1, encodeLiteral, encodeNat, List.append_assoc,
    List.append_assoc, run_ones]
  simp only [List.cons_append, List.nil_append, run_cons, Nat.zero_add]
  have h2 : step ⟨2, l.index, d, c⟩ false = ⟨3, l.index, d, c⟩ := by simp [step]
  have h3 : step ⟨3, l.index, d, c⟩ l.positive = ⟨1, l.index, d, c ++ [l]⟩ := by simp [step]
  rw [h2, h3]

lemma run_clause (n0 : ℕ) (d : List Clause) (c : Clause) (hc : c.length = 3) (w : Word) :
    ∃ n1, run ⟨0, n0, d, []⟩ (true :: encodeClause c ++ w) = run ⟨0, n1, d ++ [c], []⟩ w := by
  obtain ⟨l1, l2, l3, rfl⟩ : ∃ l1 l2 l3, c = [l1, l2, l3] := by
    match c, hc with
    | [a, b, e], _ => exact ⟨a, b, e, rfl⟩
  have h0 : step ⟨0, n0, d, []⟩ true = ⟨1, n0, d, []⟩ := by simp [step]
  have hw : encodeClause [l1, l2, l3] ++ w =
      true :: encodeLiteral l1 ++ (true :: encodeLiteral l2 ++
        (true :: encodeLiteral l3 ++ (false :: w))) := by
    simp [encodeClause, encodeList]
  rw [List.cons_append, run_cons, h0, hw, run_lit _ _ _ (by simp), run_lit _ _ _ (by simp),
    run_lit _ _ _ (by simp), run_cons]
  exact ⟨l3.index, by simp [step]⟩

lemma run_formula (F : List Clause) (hF : ∀ c ∈ F, c.length = 3) (n0 : ℕ) (d : List Clause)
    (w : Word) :
    ∃ n1, run ⟨0, n0, d, []⟩ (doneBits F ++ w) = run ⟨0, n1, d ++ F, []⟩ w := by
  induction F generalizing n0 d with
  | nil => exact ⟨n0, by simp [doneBits]⟩
  | cons c t ih =>
      obtain ⟨n1, h1⟩ := run_clause n0 d c (hF c List.mem_cons_self)
        (doneBits t ++ w)
      obtain ⟨n2, h2⟩ := ih (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc')) n1 (d ++ [c])
      refine ⟨n2, ?_⟩
      have : doneBits (c :: t) ++ w = true :: encodeClause c ++ (doneBits t ++ w) := by
        simp [doneBits]
      rw [this, h1, h2]; simp

/-- **Completeness of the scan**: it accepts the encoding of a formula of three-literal
clauses, having collected the formula. -/
theorem accept_complete (F : Formula) (hF : ∀ c ∈ F, c.length = 3) :
    (run init (encodeCNF F)).ph = 4 ∧ (run init (encodeCNF F)).done = F := by
  obtain ⟨n1, h⟩ := run_formula F hF 0 [] [false]
  have : encodeCNF F = doneBits F ++ [false] := by simp [encodeCNF, encodeList_eq, doneBits]
  rw [this, init, h]
  simp [step]

end Lax470956Proofs.ParseModel
