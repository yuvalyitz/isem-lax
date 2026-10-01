import Lax470956Proofs.Construction2Model

/-!
Construction 2's instance, stated entirely in the named language: what each of the four
kinds of job occupies, which machines may run it, the deadlines of a well-formed
formula, and the translation of a complete feasible schedule between names and numbers.

Everything after this file can be read as the paper reads, with no index arithmetic.
-/

namespace Lax470956Proofs.Construction2

open Lax470956.Scheduling Lax470956.Exact34Encoding Lax470956.Construction2

variable {x : List ℕ}

/-! ### Deadlines of a Well-Formed Formula -/

lemma dl_eq (hwf : WellFormed x) (c : Fin (nCla x)) (h : Fin 3) :
    dl x c h = 2 * (litApp x c h + 1) + 8 * (h : ℕ) :=
  dl_eq_of_lt x (hwf.app_lt c c.isLt h h.isLt) h.isLt

lemma dl_even (hwf : WellFormed x) (c : Fin (nCla x)) (h : Fin 3) : dl x c h % 2 = 0 := by
  rw [dl_eq hwf]; omega

/-- Distinct literals of one clause have distinct deadlines: the `8h` term separates the
three blocks `[2,8]`, `[10,16]`, `[18,24]`. -/
lemma dl_ne_of_ne (hwf : WellFormed x) {c : Fin (nCla x)} {h h' : Fin 3} (hne : h ≠ h') :
    dl x c h ≠ dl x c h' := by
  have h1 := hwf.app_lt c c.isLt h h.isLt
  have h2 := hwf.app_lt c c.isLt h' h'.isLt
  have h3 : (h : ℕ) ≠ (h' : ℕ) := fun hc => hne (Fin.ext hc)
  have h4 := h.isLt
  have h5 := h'.isLt
  rw [dl_eq hwf, dl_eq hwf]
  omega

/-- Distinct occurrences of the *same* variable have distinct deadlines: they carry
distinct appearance indices, and `(k, h) ↦ 2k + 8h` is injective. -/
lemma dl_ne_of_occ_ne (hwf : WellFormed x) {c c' : Fin (nCla x)} {h h' : Fin 3}
    (hvar : litVar x c h = litVar x c' h') (hne : (c, h) ≠ (c', h')) :
    dl x c h ≠ dl x c' h' := by
  have happ : litApp x c h ≠ litApp x c' h' := by
    intro hc
    obtain ⟨hc1, hc2⟩ := hwf.app_inj c c.isLt h h.isLt c' c'.isLt h' h'.isLt hvar hc
    exact hne (Prod.ext (Fin.ext hc1) (Fin.ext hc2))
  have h1 := hwf.app_lt c c.isLt h h.isLt
  have h2 := hwf.app_lt c' c'.isLt h' h'.isLt
  have h4 := h.isLt
  have h5 := h'.isLt
  rw [dl_eq hwf, dl_eq hwf]
  omega

/-! ### The Interval of Each Kind of Job -/

section Intervals

variable (x)

@[simp] lemma p_var (v : Fin (nVar x)) : (inst x).p (jIdx x (.inl v)) = 25 :=
  procOf_var x v.isLt

@[simp] lemma d_var (v : Fin (nVar x)) : (inst x).d (jIdx x (.inl v)) = 25 :=
  dueOf_var x v.isLt

@[simp] lemma start_var (v : Fin (nVar x)) : (inst x).start (jIdx x (.inl v)) = 0 := by
  simp only [Instance.start, p_var, d_var]

variable {x}

lemma p_cls (c : Fin (nCla x)) (h s : Fin 3) :
    (inst x).p (jIdx x (.inr (c, h, s)))
      = (if (s : ℕ) = 0 then 1 else if (s : ℕ) = 1 then dl x c h - 1 else 25 - dl x c h) :=
  (proc_due_elig_cls x c h s h.isLt s.isLt).1

lemma d_cls (c : Fin (nCla x)) (h s : Fin 3) :
    (inst x).d (jIdx x (.inr (c, h, s)))
      = (if (s : ℕ) = 0 then dl x c h else if (s : ℕ) = 1 then dl x c h - 1 else 25) :=
  (proc_due_elig_cls x c h s h.isLt s.isLt).2.1

@[simp] lemma p_lit (c : Fin (nCla x)) (h : Fin 3) :
    (inst x).p (jIdx x (.inr (c, h, slit))) = 1 := by rw [p_cls]; rfl

@[simp] lemma d_lit (c : Fin (nCla x)) (h : Fin 3) :
    (inst x).d (jIdx x (.inr (c, h, slit))) = dl x c h := by rw [d_cls]; rfl

@[simp] lemma p_alpha (c : Fin (nCla x)) (h : Fin 3) :
    (inst x).p (jIdx x (.inr (c, h, salpha))) = dl x c h - 1 := by rw [p_cls]; rfl

@[simp] lemma d_alpha (c : Fin (nCla x)) (h : Fin 3) :
    (inst x).d (jIdx x (.inr (c, h, salpha))) = dl x c h - 1 := by rw [d_cls]; rfl

@[simp] lemma p_omega (c : Fin (nCla x)) (h : Fin 3) :
    (inst x).p (jIdx x (.inr (c, h, somega))) = 25 - dl x c h := by rw [p_cls]; rfl

@[simp] lemma d_omega (c : Fin (nCla x)) (h : Fin 3) :
    (inst x).d (jIdx x (.inr (c, h, somega))) = 25 := by rw [d_cls]; rfl

@[simp] lemma start_lit (c : Fin (nCla x)) (h : Fin 3) :
    (inst x).start (jIdx x (.inr (c, h, slit))) = dl x c h - 1 := by
  simp only [Instance.start, p_lit, d_lit]

@[simp] lemma start_alpha (c : Fin (nCla x)) (h : Fin 3) :
    (inst x).start (jIdx x (.inr (c, h, salpha))) = 0 := by
  simp only [Instance.start, p_alpha, d_alpha, Nat.sub_self]

@[simp] lemma start_omega (c : Fin (nCla x)) (h : Fin 3) :
    (inst x).start (jIdx x (.inr (c, h, somega))) = dl x c h := by
  have := dl_le x (c : ℕ) (h : ℕ)
  simp only [Instance.start, p_omega, d_omega]
  omega

end Intervals

/-! ### Eligible Machines, Named -/

/-- Two named machines are equal exactly when their numbers are. -/
lemma mIdx_val_inj {i i' : MachS x} (h : (mIdx x i : ℕ) = (mIdx x i' : ℕ)) : i = i' :=
  mIdx_injective x (Fin.ext h)

/-- The variable of a literal of a well-formed formula, as an index. -/
def litVarF (hwf : WellFormed x) (c : Fin (nCla x)) (h : Fin 3) : Fin (nVar x) :=
  ⟨litVar x c h, hwf.var_lt c c.isLt h h.isLt⟩

/-- The sign of a literal, as a Boolean. -/
def litSignB (x : List ℕ) (c h : ℕ) : Bool := decide (litSign x c h = 1)

lemma mem_pair {a b v : ℕ} : v ∈ [a, b] ↔ v = a ∨ v = b := by simp

lemma mem_triple {a b c v : ℕ} : v ∈ [a, b, c] ↔ v = a ∨ v = b ∨ v = c := by simp

lemma elig_var {v : Fin (nVar x)} {i : MachS x} :
    mIdx x i ∈ (inst x).eligible (jIdx x (.inl v)) ↔ i = .inl (v, true) ∨ i = .inl (v, false) := by
  rw [mem_eligible]
  show (mIdx x i : ℕ) ∈ eligOf x (v : ℕ) ↔ _
  rw [eligOf_var x v.isLt, mem_pair]
  constructor
  · rintro (h | h)
    · exact Or.inl (mIdx_val_inj (x := x) (i' := .inl (v, true)) h)
    · exact Or.inr (mIdx_val_inj (x := x) (i' := .inl (v, false)) h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

lemma elig_wrap {c : Fin (nCla x)} {h s : Fin 3} (hs : s ≠ slit) {i : MachS x} :
    mIdx x i ∈ (inst x).eligible (jIdx x (.inr (c, h, s))) ↔
      i = .inr (c, 0) ∨ i = .inr (c, 1) ∨ i = .inr (c, 2) := by
  have hs0 : (s : ℕ) ≠ 0 := fun hc => hs (Fin.ext hc)
  rw [mem_eligible]
  show (mIdx x i : ℕ) ∈ eligOf x (nVar x + 9 * (c : ℕ) + 3 * (h : ℕ) + (s : ℕ)) ↔ _
  rw [(proc_due_elig_cls x c h s h.isLt s.isLt).2.2, if_neg hs0, mem_triple]
  constructor
  · rintro (hh | hh | hh)
    · exact Or.inl (mIdx_val_inj (x := x) (i' := .inr (c, 0)) (by rw [hh]; rfl))
    · exact Or.inr (Or.inl (mIdx_val_inj (x := x) (i' := .inr (c, 1)) (by rw [hh]; rfl)))
    · exact Or.inr (Or.inr (mIdx_val_inj (x := x) (i' := .inr (c, 2)) (by rw [hh]; rfl)))
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

lemma elig_lit (hwf : WellFormed x) {c : Fin (nCla x)} {h : Fin 3} {i : MachS x} :
    mIdx x i ∈ (inst x).eligible (jIdx x (.inr (c, h, slit))) ↔
      i = .inr (c, 1) ∨ i = .inr (c, 2) ∨
        i = .inl (litVarF hwf c h, litSignB x c h) := by
  rw [mem_eligible]
  show (mIdx x i : ℕ) ∈ eligOf x (nVar x + 9 * (c : ℕ) + 3 * (h : ℕ) + (slit : ℕ)) ↔ _
  rw [(proc_due_elig_cls x c h (slit) h.isLt (by decide)).2.2, if_pos (show ((slit : ℕ)) = 0 from rfl), mem_triple]
  have hvm : (mIdx x (.inl (litVarF hwf c h, litSignB x c h)) : ℕ)
      = 2 * litVar x c h + (if litSign x c h = 1 then 0 else 1) := by
    simp only [litSignB, litVarF]
    by_cases hp : litSign x c h = 1
    · simp [hp, mIdx]
    · simp [hp, mIdx]
  constructor
  · rintro (hh | hh | hh)
    · exact Or.inl (mIdx_val_inj (x := x) (i' := .inr (c, 1)) (by rw [hh]; rfl))
    · exact Or.inr (Or.inl (mIdx_val_inj (x := x) (i' := .inr (c, 2)) (by rw [hh]; rfl)))
    · exact Or.inr (Or.inr (mIdx_val_inj (x := x) (i' := _) (by rw [hh, hvm])))
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hvm)

end Lax470956Proofs.Construction2
