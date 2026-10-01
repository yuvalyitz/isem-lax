import Lax470956Proofs.Construction2Sched

/-!
**Lemma 3.** A satisfying assignment yields a feasible schedule placing every job.

The variable job of `v` goes on the machine *opposing* its truth value, leaving the
machine that agrees with it free for the selected literal of each clause satisfied by
`v`. Within a clause, the selected literal's job takes that variable machine, and the
remaining jobs are distributed over the clause's own three machines by the transposition
exchanging the selected literal with `0` — so the selected literal's two wrappers take
machine `0`, where no literal job is eligible.
-/

namespace Lax470956Proofs.Construction2

open Lax470956.Scheduling Lax470956.Exact34Encoding Lax470956.Construction2

variable {x : List ℕ}

/-! ### Non-Overlap of a Chain of Three Jobs -/

private lemma ovl_symm {I : Instance} {j j' : Fin I.jobs} (h : I.Overlap j j') :
    I.Overlap j' j := ⟨h.2, h.1⟩

private lemma not_ovl_of_le {I : Instance} {j j' : Fin I.jobs} (h : I.d j ≤ I.start j') :
    ¬ I.Overlap j j' := fun hc => absurd hc.2 (Nat.not_lt.mpr h)

private lemma start_le_d {I : Instance} (j : Fin I.jobs) : I.start j ≤ I.d j := Nat.sub_le _ _

/-- Three jobs laid out one after another are pairwise non-overlapping. -/
private lemma not_ovl_chain3 {I : Instance} {j₁ j₂ j₃ : Fin I.jobs}
    (h₁ : I.d j₁ ≤ I.start j₂) (h₂ : I.d j₂ ≤ I.start j₃)
    {j j' : Fin I.jobs} (hj : j = j₁ ∨ j = j₂ ∨ j = j₃)
    (hj' : j' = j₁ ∨ j' = j₂ ∨ j' = j₃) (hne : j ≠ j') : ¬ I.Overlap j j' := by
  have s₁ := start_le_d j₁
  have s₂ := start_le_d j₂
  have s₃ := start_le_d j₃
  rcases hj with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | exact not_ovl_of_le (by omega)
      | exact fun hc => not_ovl_of_le (by omega) (ovl_symm hc)

/-! ### The Transposition That Distributes a Clause's Jobs -/

lemma fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by revert a; decide

lemma swap_eq_zero_iff (a b : Fin 3) : Equiv.swap a 0 b = 0 ↔ b = a := by
  constructor
  · intro hh
    have h2 := congrArg (Equiv.swap a 0) hh
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
  · rintro rfl
    exact Equiv.swap_apply_left _ _

/-! ### The Schedule -/

variable (hwf : WellFormed x) (τ : ℕ → Bool) (sel : Fin (nCla x) → Fin 3)

/-- The schedule of Lemma 3. -/
def satSchedule : SchedS x
  | .inl v => some (.inl (v, !τ (v : ℕ)))
  | .inr (c, h, s) =>
      if s = slit ∧ h = sel c then some (.inl (litVarF hwf c h, litSignB x c h))
      else some (.inr (c, Equiv.swap (sel c) 0 h))

lemma satSchedule_ne_none (a : JobS x) : satSchedule hwf τ sel a ≠ none := by
  match a with
  | .inl _ => simp [satSchedule]
  | .inr (_, _, _) => simp only [satSchedule]; split <;> simp

lemma satSchedule_elig (a : JobS x) (i : MachS x)
    (h : satSchedule hwf τ sel a = some i) :
    mIdx x i ∈ (inst x).eligible (jIdx x a) := by
  match a with
  | .inl v =>
      simp only [satSchedule] at h
      have hi : i = .inl (v, !τ (v : ℕ)) := (Option.some.inj h).symm
      subst hi
      rw [elig_var]
      cases τ (v : ℕ) <;> simp
  | .inr (c, hh, s) =>
      simp only [satSchedule] at h
      split at h
      · rename_i hcond
        obtain ⟨rfl, rfl⟩ := hcond
        have hi : i = .inl (litVarF hwf c (sel c), litSignB x c (sel c)) :=
          (Option.some.inj h).symm
        subst hi
        rw [elig_lit hwf]
        exact Or.inr (Or.inr rfl)
      · rename_i hcond
        have hi : i = .inr (c, Equiv.swap (sel c) 0 hh) := (Option.some.inj h).symm
        subst hi
        by_cases hs : s = slit
        · subst hs
          have hne : hh ≠ sel c := fun hc => hcond ⟨rfl, hc⟩
          have h0 : Equiv.swap (sel c) 0 hh ≠ 0 := fun hc => hne ((swap_eq_zero_iff _ _).mp hc)
          rw [elig_lit hwf]
          rcases fin3_cases (Equiv.swap (sel c) 0 hh) with h1 | h1 | h1
          · exact absurd h1 h0
          · exact Or.inl (by rw [h1])
          · exact Or.inr (Or.inl (by rw [h1]))
        · rw [elig_wrap hs]
          rcases fin3_cases (Equiv.swap (sel c) 0 hh) with h1 | h1 | h1 <;> rw [h1] <;> simp

/-- Only the variable job of `v` and the selected literal jobs of `v` reach a variable
machine, and they land on *opposite* machines. -/
lemma satSchedule_var_machine
    (hsel : ∀ c : Fin (nCla x), litSignB x c (sel c) = τ (litVar x c (sel c)))
    {a : JobS x} {v : Fin (nVar x)} {b : Bool}
    (h : satSchedule hwf τ sel a = some (.inl (v, b))) :
    (a = .inl v ∧ b = !τ (v : ℕ)) ∨
      (∃ c, a = .inr (c, sel c, slit) ∧ litVarF hwf c (sel c) = v ∧ b = τ (v : ℕ)) := by
  match a with
  | .inl u =>
      have h2 : (Sum.inl (u, !τ (u : ℕ)) : MachS x) = Sum.inl (v, b) := Option.some.inj h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨rfl, rfl⟩
  | .inr (c, hh, s) =>
      simp only [satSchedule] at h
      split at h
      · rename_i hcond
        obtain ⟨rfl, rfl⟩ := hcond
        have h2 : (Sum.inl (litVarF hwf c (sel c), litSignB x c (sel c)) : MachS x)
            = Sum.inl (v, b) := Option.some.inj h
        simp only [Sum.inl.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        refine Or.inr ⟨c, rfl, rfl, ?_⟩
        rw [hsel c]
        rfl
      · exact absurd (Option.some.inj h) (by simp)

/-- Only the three jobs of a single literal occurrence reach a given clause machine. -/
lemma satSchedule_clause_machine {a : JobS x} {c : Fin (nCla x)} {t : Fin 3}
    (h : satSchedule hwf τ sel a = some (.inr (c, t))) :
    ∃ h₀ : Fin 3, Equiv.swap (sel c) 0 h₀ = t ∧
      (a = .inr (c, h₀, slit) ∨ a = .inr (c, h₀, salpha) ∨ a = .inr (c, h₀, somega)) := by
  match a with
  | .inl _ => exact absurd (Option.some.inj h) (by simp)
  | .inr (c', hh, s) =>
      simp only [satSchedule] at h
      split at h
      · exact absurd (Option.some.inj h) (by simp)
      · have h2 : (Sum.inr (c', Equiv.swap (sel c') 0 hh) : MachS x) = Sum.inr (c, t) :=
          Option.some.inj h
        simp only [Sum.inr.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        refine ⟨hh, rfl, ?_⟩
        rcases fin3_cases s with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)

/-- **Lemma 3, feasibility.** -/
theorem satSchedule_feasible
    (hsel : ∀ c : Fin (nCla x), litSignB x c (sel c) = τ (litVar x c (sel c))) :
    FeasibleS (satSchedule hwf τ sel) := by
  refine ⟨satSchedule_elig hwf τ sel, ?_⟩
  intro a a' i hne hov hj hj'
  refine absurd hov ?_
  match i with
  | .inl (v, b) =>
      rcases satSchedule_var_machine hwf τ sel hsel hj with ⟨rfl, hb⟩ | ⟨c, rfl, hvc, hb⟩
      · rcases satSchedule_var_machine hwf τ sel hsel hj' with ⟨rfl, hb'⟩ | ⟨c', rfl, hvc', hb'⟩
        · exact absurd rfl hne
        · exfalso; rw [hb] at hb'; cases hbb : τ (v : ℕ) <;> rw [hbb] at hb' <;> simp at hb'
      · rcases satSchedule_var_machine hwf τ sel hsel hj' with ⟨rfl, hb'⟩ | ⟨c', rfl, hvc', hb'⟩
        · exfalso; rw [hb] at hb'; cases hbb : τ (v : ℕ) <;> rw [hbb] at hb' <;> simp at hb'
        · have hvv : litVar x c (sel c) = litVar x c' (sel c') :=
            congrArg Fin.val (hvc.trans hvc'.symm)
          have hocc : (c, sel c) ≠ (c', sel c') := by
            intro hc
            apply hne
            rw [Prod.ext_iff] at hc
            simp only at hc
            obtain ⟨rfl, h2⟩ := hc
            rw [h2]
          have hdne := dl_ne_of_occ_ne hwf hvv hocc
          have hd1 := dl_ge x (c : ℕ) ((sel c : ℕ))
          have hd2 := dl_ge x (c' : ℕ) ((sel c' : ℕ))
          intro hc
          obtain ⟨ha, hbb⟩ := hc
          rw [start_lit, d_lit] at ha
          rw [start_lit, d_lit] at hbb
          omega
  | .inr (c, t) =>
      obtain ⟨h₀, ht₀, hjj⟩ := satSchedule_clause_machine hwf τ sel hj
      obtain ⟨h₁, ht₁, hjj'⟩ := satSchedule_clause_machine hwf τ sel hj'
      have hh : h₀ = h₁ := (Equiv.swap (sel c) 0).injective (ht₀.trans ht₁.symm)
      subst hh
      refine not_ovl_chain3
        (j₁ := jIdx x (.inr (c, h₀, salpha))) (j₂ := jIdx x (.inr (c, h₀, slit)))
        (j₃ := jIdx x (.inr (c, h₀, somega))) ?_ ?_ ?_ ?_ (fun hc => hne (jIdx_injective x hc))
      · rw [d_alpha, start_lit]
      · rw [d_lit, start_omega]
      · rcases hjj with h1 | h1 | h1
        · exact Or.inr (Or.inl (by rw [h1]))
        · exact Or.inl (by rw [h1])
        · exact Or.inr (Or.inr (by rw [h1]))
      · rcases hjj' with h1 | h1 | h1
        · exact Or.inr (Or.inl (by rw [h1]))
        · exact Or.inl (by rw [h1])
        · exact Or.inr (Or.inr (by rw [h1]))

/-- **Lemma 3.** A satisfying assignment yields a feasible schedule placing every job. -/
theorem lemma3 (hwf : WellFormed x) (h : ∃ τ, Satisfies x τ) : (inst x).AllSchedulable := by
  obtain ⟨τ, hτ⟩ := h
  have hex : ∀ c : Fin (nCla x), ∃ hh : Fin 3, litSignB x c hh = τ (litVar x c hh) := by
    intro c
    obtain ⟨hh, hhlt, hsat⟩ := hτ (c : ℕ) c.isLt
    exact ⟨⟨hh, hhlt⟩, by simp only [litSignB, hsat, Bool.decide_eq_true]⟩
  choose sel hsel using hex
  exact allSchedulable_of_named (satSchedule_feasible hwf τ sel hsel)
    (satSchedule_ne_none hwf τ sel)

end Lax470956Proofs.Construction2
