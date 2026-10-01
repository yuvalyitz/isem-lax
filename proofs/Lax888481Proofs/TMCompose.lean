import Lax434930Proofs.PolynomialComposition

set_option backward.isDefEq.respectTransparency false

/-!
Sequential composition of two polynomial-time Turing machines through an intermediate
word over an arbitrary finite alphabet.

The archive's composition theorem asks for a binary intermediate encoding, because that
is what the complexity classes it was written for use. The equivalence between word RAMs
and Turing machines speaks a three-letter alphabet — a separator and two digits — so a
reduction computed on a word RAM cannot be composed with a binary one as it stands. This
file is that theorem with the alphabet of the transfer stack made a parameter; the
construction and its proof are otherwise the archive's.
-/

namespace Lax888481Proofs.TMCompose

open Turing Lax434930Proofs Lax434930Proofs.TM2Bounds Polynomial

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (M N : FinTM2) (Γm : Type) [Fintype Γm] [Inhabited Γm]

abbrev Key := M.K ⊕ (N.K ⊕ Unit)
abbrev Label := M.Λ ⊕ (Bool ⊕ N.Λ)
abbrev State := M.σ × (N.σ × Option Γm)

def Alphabet : Key M N → Type
  | .inl k => M.Γ k
  | .inr (.inl k) => N.Γ k
  | .inr (.inr _) => Γm

abbrev Cfg := TM2.Cfg (Alphabet M N Γm) (Label M N) (State M N Γm)
abbrev Stmt := TM2.Stmt (Alphabet M N Γm) (Label M N) (State M N Γm)

def joinedStacks (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp : List Γm) : (k : Key M N) → List (Alphabet M N Γm k)
  | .inl k => s k
  | .inr (.inl k) => t k
  | .inr (.inr _) => tmp

theorem update_left (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp : List Γm) (k : M.K) (xs : List (M.Γ k)) :
    Function.update (joinedStacks M N Γm s t tmp) (.inl k) xs =
      joinedStacks M N Γm (Function.update s k xs) t tmp := by
  funext j
  cases j with
  | inl j => by_cases hj : j = k <;> simp_all [joinedStacks] <;> rfl
  | inr j => cases j <;> simp [joinedStacks]

theorem update_right (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp : List Γm) (k : N.K) (xs : List (N.Γ k)) :
    Function.update (joinedStacks M N Γm s t tmp) (.inr (.inl k)) xs =
      joinedStacks M N Γm s (Function.update t k xs) tmp := by
  funext j
  cases j with
  | inl j => simp [joinedStacks]
  | inr j =>
      cases j with
      | inl j => by_cases hj : j = k <;> simp_all [joinedStacks] <;> rfl
      | inr j => simp [joinedStacks]

theorem update_tmp (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp xs : List Γm) :
    Function.update (joinedStacks M N Γm s t tmp) (.inr (.inr ())) xs = joinedStacks M N Γm s t xs := by
  funext j
  cases j with
  | inl j => simp [joinedStacks]
  | inr j => cases j <;> simp [joinedStacks]

def leftStmt : M.Stmt → Stmt M N Γm
  | .push k f q => .push (.inl k) (fun v => f v.1) (leftStmt q)
  | .pop k f q => .pop (.inl k) (fun v b => (f v.1 b, v.2)) (leftStmt q)
  | .peek k f q => .peek (.inl k) (fun v b => (f v.1 b, v.2)) (leftStmt q)
  | .load f q => .load (fun v => (f v.1, v.2)) (leftStmt q)
  | .branch f p q => .branch (fun v => f v.1) (leftStmt p) (leftStmt q)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .goto (fun _ => .inr (.inl false))

def rightStmt : N.Stmt → Stmt M N Γm
  | .push k f q => .push (.inr (.inl k)) (fun v => f v.2.1) (rightStmt q)
  | .pop k f q => .pop (.inr (.inl k)) (fun v b => (v.1, f v.2.1 b, v.2.2)) (rightStmt q)
  | .peek k f q => .peek (.inr (.inl k)) (fun v b => (v.1, f v.2.1 b, v.2.2)) (rightStmt q)
  | .load f q => .load (fun v => (v.1, f v.2.1, v.2.2)) (rightStmt q)
  | .branch f p q => .branch (fun v => f v.2.1) (rightStmt p) (rightStmt q)
  | .goto f => .goto (fun v => .inr (.inr (f v.2.1)))
  | .halt => .halt

def leftCfg (c : M.Cfg) : Cfg M N Γm where
  l := some (c.l.elim (.inr (.inl false)) Sum.inl)
  var := (c.var, N.initialState, none)
  stk := joinedStacks M N Γm c.stk (fun _ => []) []

def rightCfg (c : N.Cfg) : Cfg M N Γm where
  l := c.l.map (fun l => .inr (.inr l))
  var := (M.initialState, c.var, none)
  stk := joinedStacks M N Γm (fun _ => []) c.stk []

theorem left_stepAux (q : M.Stmt) (v : M.σ) (s : (k : M.K) → List (M.Γ k)) :
    TM2.stepAux (leftStmt M N Γm q) (v, N.initialState, none)
      (joinedStacks M N Γm s (fun _ => []) []) = leftCfg M N Γm (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simpa only [leftStmt, TM2.stepAux, update_left] using! ih v _
  | pop k f q ih =>
      simpa only [leftStmt, TM2.stepAux, joinedStacks, update_left] using! ih (f v (s k).head?) _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq => cases hf : f v <;> simp [leftStmt, TM2.stepAux, hf, ihp, ihq]
  | goto f => rfl
  | halt => rfl

theorem right_stepAux (q : N.Stmt) (v : N.σ) (s : (k : N.K) → List (N.Γ k)) :
    TM2.stepAux (rightStmt M N Γm q) (M.initialState, v, none)
      (joinedStacks M N Γm (fun _ => []) s []) = rightCfg M N Γm (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simpa only [rightStmt, TM2.stepAux, update_right] using! ih v _
  | pop k f q ih =>
      simpa only [rightStmt, TM2.stepAux, joinedStacks, update_right] using! ih (f v (s k).head?) _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq => cases hf : f v <;> simp [rightStmt, TM2.stepAux, hf, ihp, ihq]
  | goto f => rfl
  | halt => rfl

variable (out : M.Γ M.k₁ ≃ Γm) (inp : N.Γ N.k₀ ≃ Γm)

def firstTransfer : Stmt M N Γm :=
  .pop (.inl M.k₁) (fun v b => (v.1, v.2.1, b.map out))
    (.branch (fun v => v.2.2.isSome)
      (.push (.inr (.inr ())) (fun v => v.2.2.getD default)
        (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => .inr (.inl false)))))
      (.goto (fun _ => .inr (.inl true))))

def secondTransfer : Stmt M N Γm :=
  .pop (.inr (.inr ())) (fun v b => (v.1, v.2.1, b))
    (.branch (fun v => v.2.2.isSome)
      (.push (.inr (.inl N.k₀)) (fun v => inp.symm (v.2.2.getD default))
        (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => .inr (.inl true)))))
      (.goto (fun _ => .inr (.inr N.main))))

def code : Label M N → Stmt M N Γm
  | .inl l => leftStmt M N Γm (M.m l)
  | .inr (.inl false) => firstTransfer M N Γm out
  | .inr (.inl true) => secondTransfer M N Γm inp
  | .inr (.inr l) => rightStmt M N Γm (N.m l)

def machine : FinTM2 where
  K := Key M N
  k₀ := .inl M.k₀
  k₁ := .inr (.inl N.k₁)
  Γ := Alphabet M N Γm
  Γk₀Fin := M.Γk₀Fin
  Λ := Label M N
  main := .inl M.main
  σ := State M N Γm
  initialState := (M.initialState, N.initialState, none)
  m := code M N Γm out inp

theorem left_step {c d : M.Cfg} (h : M.step c = some d) :
    (machine M N Γm out inp).step (leftCfg M N Γm c) = some (leftCfg M N Γm d) := by
  cases c with
  | mk l v s =>
      cases l with
      | none => simp [FinTM2.step, TM2.step] at h
      | some l =>
          have hd : TM2.stepAux (M.m l) v s = d := Option.some.inj h
          rw [← hd]
          exact congrArg some (left_stepAux M N Γm (M.m l) v s)

theorem right_step {c d : N.Cfg} (h : N.step c = some d) :
    (machine M N Γm out inp).step (rightCfg M N Γm c) = some (rightCfg M N Γm d) := by
  cases c with
  | mk l v s =>
      cases l with
      | none => simp [FinTM2.step, TM2.step] at h
      | some l =>
          have hd : TM2.stepAux (N.m l) v s = d := Option.some.inj h
          rw [← hd]
          exact congrArg some (right_stepAux M N Γm (N.m l) v s)

def single {K : Type} [DecidableEq K] (Γ : K → Type) (port : K) (xs : List (Γ port)) :
    (k : K) → List (Γ k) := Function.update (fun _ => []) port xs

def firstCfg (xs : List (M.Γ M.k₁)) (tmp : List Γm) : Cfg M N Γm where
  l := some (.inr (.inl false))
  var := (M.initialState, N.initialState, none)
  stk := joinedStacks M N Γm (single M.Γ M.k₁ xs) (fun _ => []) tmp

def secondCfg (tmp : List Γm) (ys : List (N.Γ N.k₀)) : Cfg M N Γm where
  l := some (.inr (.inl true))
  var := (M.initialState, N.initialState, none)
  stk := joinedStacks M N Γm (fun _ => []) (single N.Γ N.k₀ ys) tmp

theorem first_cons (x : M.Γ M.k₁) (xs : List (M.Γ M.k₁)) (tmp : List Γm) :
    (machine M N Γm out inp).step (firstCfg M N Γm (x :: xs) tmp) =
      some (firstCfg M N Γm xs (out x :: tmp)) := by
  simp [FinTM2.step, machine, code, firstTransfer, firstCfg, TM2.step, TM2.stepAux,
    update_left, update_tmp, joinedStacks, single, List.head?, List.tail]

theorem first_nil (tmp : List Γm) :
    (machine M N Γm out inp).step (firstCfg M N Γm [] tmp) = some (secondCfg M N Γm tmp []) := by
  simp [FinTM2.step, machine, code, firstTransfer, firstCfg, secondCfg, TM2.step, TM2.stepAux,
    update_left, joinedStacks, single, List.head?, List.tail]

theorem second_cons (b : Γm) (tmp : List Γm) (ys : List (N.Γ N.k₀)) :
    (machine M N Γm out inp).step (secondCfg M N Γm (b :: tmp) ys) =
      some (secondCfg M N Γm tmp (inp.symm b :: ys)) := by
  simp [FinTM2.step, machine, code, secondTransfer, secondCfg, TM2.step, TM2.stepAux,
    update_right, update_tmp, joinedStacks, single, List.head?, List.tail]

theorem second_nil (ys : List (N.Γ N.k₀)) :
    (machine M N Γm out inp).step (secondCfg M N Γm [] ys) = some (rightCfg M N Γm (initList N ys)) := by
  simp [FinTM2.step, machine, code, secondTransfer, secondCfg, rightCfg,
    TM2.step, TM2.stepAux, update_tmp, joinedStacks, single, initList, Function.update,
    List.head?, List.tail]
  congr 2
  funext k
  by_cases hk : k = N.k₀
  · subst k; simp
  · simp [hk]

theorem first_run (xs : List (M.Γ M.k₁)) (tmp : List Γm) :
    (fun c : Option (Cfg M N Γm) => c.bind (machine M N Γm out inp).step)^[xs.length + 1]
      (some (firstCfg M N Γm xs tmp)) =
      some (secondCfg M N Γm ((xs.map out).reverse ++ tmp) []) := by
  induction xs generalizing tmp with
  | nil => simpa using first_nil M N Γm out inp tmp
  | cons x xs ih =>
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, Option.bind_some,
        first_cons, ih]
      simp

theorem second_run (tmp : List Γm) (ys : List (N.Γ N.k₀)) :
    (fun c : Option (Cfg M N Γm) => c.bind (machine M N Γm out inp).step)^[tmp.length + 1]
      (some (secondCfg M N Γm tmp ys)) =
      some (rightCfg M N Γm (initList N (tmp.reverse.map inp.symm ++ ys))) := by
  induction tmp generalizing ys with
  | nil => simpa using second_nil M N Γm out inp ys
  | cons b tmp ih =>
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, Option.bind_some,
        second_cons, ih]
      simp

theorem left_halt (xs : List (M.Γ M.k₁)) : leftCfg M N Γm (haltList M xs) = firstCfg M N Γm xs [] := by
  simp [leftCfg, haltList, firstCfg, single, Function.update]
  congr 1
  funext k
  by_cases hk : k = M.k₁
  · subst k; simp
  · simp [hk]

/-- Exactly two linear transfers, including their end-of-stack tests. -/
theorem transfer_run (xs : List (M.Γ M.k₁)) :
    (fun c : Option (Cfg M N Γm) => c.bind (machine M N Γm out inp).step)^[2 * xs.length + 2]
      (some (leftCfg M N Γm (haltList M xs))) =
      some (rightCfg M N Γm (initList N ((xs.map out).map inp.symm))) := by
  have h₁ := first_run M N Γm out inp xs []
  have h₂ := second_run M N Γm out inp (xs.map out).reverse []
  simp only [List.append_nil] at h₁
  simp only [List.length_reverse, List.length_map, List.reverse_reverse, List.append_nil] at h₂
  have h := append_run (machine M N Γm out inp).step h₁ h₂
  rw [left_halt]
  simpa only [show xs.length + 1 + (xs.length + 1) = 2 * xs.length + 2 by omega] using! h

theorem initial_eq (xs : List (M.Γ M.k₀)) :
    initList (machine M N Γm out inp) xs = leftCfg M N Γm (initList M xs) := by
  apply cfg_ext
  · rfl
  · rfl
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = M.k₀
      · subst k; simp [initList, machine, leftCfg, joinedStacks]
      · simp [initList, machine, leftCfg, joinedStacks, hk]
  | inr k => cases k <;> simp [initList, machine, leftCfg, joinedStacks]

theorem terminal_eq (ys : List (N.Γ N.k₁)) :
    rightCfg M N Γm (haltList N ys) = haltList (machine M N Γm out inp) ys := by
  apply cfg_ext
  · rfl
  · rfl
  funext k
  cases k with
  | inl k => simp [haltList, machine, rightCfg, joinedStacks]
  | inr k =>
      cases k with
      | inl k =>
          by_cases hk : k = N.k₁
          · subst k; simp [haltList, machine, rightCfg, joinedStacks]
          · simp [haltList, machine, rightCfg, joinedStacks, hk]
      | inr k => simp [haltList, machine, rightCfg, joinedStacks]

theorem eval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using Nat.add_le_add hp hq
  | monomial k c =>
      simp only [eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

/-- Composition of polynomial-time functions with a binary intermediate encoding. -/
theorem comp {α β γ αΓ γΓ : Type} {eα : α → List αΓ} {Γm : Type} [Fintype Γm] [Inhabited Γm] {eβ : β → List Γm}
    {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by
  classical
  let q : Polynomial ℕ := X + C (factor h₁.tm) * h₁.time
  let p : Polynomial ℕ := h₁.time + 2 * q + 2 + h₂.time.comp q
  let T := machine h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet
  refine ⟨{ tm := T
            inputAlphabet := h₁.inputAlphabet
            outputAlphabet := h₂.outputAlphabet
            time := p
            outputsFun := ?_ }⟩
  intro a
  let r₁ := h₁.outputsFun a
  let r₂ := h₂.outputsFun (f a)
  have hl : (eβ (f a)).length ≤ q.eval (eα a).length := by
    have h := output_length h₁.tm r₁
    simpa [q] using h
  have ht₂ : h₂.time.eval (eβ (f a)).length ≤ h₂.time.eval (q.eval (eα a).length) :=
    eval_mono h₂.time hl
  have hfirst := lift_run h₁.tm.step T.step (leftCfg h₁.tm h₂.tm Γm)
    (fun _ _ h => left_step h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet h)
    r₁.steps r₁.evals_in_steps
  have hcopy := transfer_run h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet
    ((eβ (f a)).map h₁.outputAlphabet.invFun)
  have hmiddle :
      (((eβ (f a)).map h₁.outputAlphabet.invFun).map h₁.outputAlphabet).map
        h₂.inputAlphabet.symm = (eβ (f a)).map h₂.inputAlphabet.invFun := by
    simp [List.map_map, Function.comp_def]
  rw [hmiddle] at hcopy
  have hsecond := lift_run h₂.tm.step T.step (rightCfg h₁.tm h₂.tm Γm)
    (fun _ _ h => right_step h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet h)
    r₂.steps r₂.evals_in_steps
  have hfull := append_run T.step (append_run T.step hfirst hcopy) hsecond
  refine ⟨⟨r₁.steps + (2 * (eβ (f a)).length + 2) + r₂.steps, ?_⟩, ?_⟩
  · simpa only [List.length_map, initial_eq,
      terminal_eq h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet, Function.comp_apply, T,
      Option.map_some] using! hfull
  · have hb₁ := r₁.steps_le_m
    have hb₂ := r₂.steps_le_m
    change r₁.steps ≤ h₁.time.eval (eα a).length at hb₁
    change r₂.steps ≤ h₂.time.eval (eβ (f a)).length at hb₂
    dsimp only [p]
    simp only [eval_add, eval_mul, eval_ofNat, eval_comp]
    omega

end Lax888481Proofs.TMCompose
