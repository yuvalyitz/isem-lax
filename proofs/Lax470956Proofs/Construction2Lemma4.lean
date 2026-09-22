import Lax470956Proofs.Construction2Lemma3
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
**Observation 4** and **Lemma 4**: a feasible schedule placing every job yields a
satisfying assignment.

All three `α`-jobs of a clause start at `0`, so they pairwise overlap and are spread
bijectively over the clause's three machines; the same holds for the `ω`-jobs, which all
end at `25`. If `α^(h)` shares a machine with `ω^(ρ h)` then `d_h - 1 ≤ d_{ρ h}`, and
since all deadlines are even this is `d_h ≤ d_{ρ h}`. Summing over `h` and using that
`ρ` is a bijection turns every one of those inequalities into an equality, so `ρ` is the
identity and each literal's two wrappers share a machine.

Machine `0` of a clause is then blocked for two of its literals, and the third literal
job has nowhere to go but its variable machine — which forces the variable job onto the
opposite machine, and that is the assignment.
-/

namespace Lax470956Proofs.Construction2

open Lax470956.Scheduling Lax470956.Exact34Encoding Lax470956.Construction2

variable {x : List ℕ}

private lemma not_ovl_iff {I : Instance} {j j' : Fin I.jobs} :
    ¬ I.Overlap j j' ↔ (I.d j' ≤ I.start j ∨ I.d j ≤ I.start j') := by
  simp only [Instance.Overlap, not_and_or, Nat.not_lt]

private lemma job_ne_idx {c c' : Fin (nCla x)} {h h' s s' : Fin 3} (hh : h ≠ h') :
    (Sum.inr (c, h, s) : JobS x) ≠ Sum.inr (c', h', s') := fun he =>
  hh (congrArg (fun q : Fin (nCla x) × Fin 3 × Fin 3 => q.2.1) (Sum.inr.inj he))

private lemma job_ne_slot {c c' : Fin (nCla x)} {h h' s s' : Fin 3} (hs : s ≠ s') :
    (Sum.inr (c, h, s) : JobS x) ≠ Sum.inr (c', h', s') := fun he =>
  hs (congrArg (fun q : Fin (nCla x) × Fin 3 × Fin 3 => q.2.2) (Sum.inr.inj he))

private lemma job_var_ne {v : Fin (nVar x)} {y : Fin (nCla x) × Fin 3 × Fin 3} :
    (Sum.inl v : JobS x) ≠ Sum.inr y := by simp

section Lemma4

variable {σ : SchedS x} (hfeas : FeasibleS σ) (hall : ∀ a, σ a ≠ none)

include hfeas hall in
lemma alpha_machine (c : Fin (nCla x)) (h : Fin 3) :
    ∃ t : Fin 3, σ (.inr (c, h, salpha)) = some (.inr (c, t)) := by
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp (hall (.inr (c, h, salpha)))
  rcases (elig_wrap (x := x) (c := c) (h := h) (s := salpha) (by decide)).mp
    (hfeas.1 _ _ hi) with rfl | rfl | rfl
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · exact ⟨2, hi⟩

include hfeas hall in
lemma omega_machine (c : Fin (nCla x)) (h : Fin 3) :
    ∃ t : Fin 3, σ (.inr (c, h, somega)) = some (.inr (c, t)) := by
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp (hall (.inr (c, h, somega)))
  rcases (elig_wrap (x := x) (c := c) (h := h) (s := somega) (by decide)).mp
    (hfeas.1 _ _ hi) with rfl | rfl | rfl
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · exact ⟨2, hi⟩

include hfeas hall in
/-- **Observation 4.** In a schedule placing every job, the two wrapper jobs of each
literal share a machine, and the assignment of literals to the clause's three machines
is a bijection. -/
theorem observation4 (hwf : WellFormed x) (c : Fin (nCla x)) :
    ∃ ρ : Fin 3 → Fin 3, Function.Bijective ρ ∧
      ∀ h, σ (.inr (c, h, salpha)) = some (.inr (c, ρ h)) ∧
        σ (.inr (c, h, somega)) = some (.inr (c, ρ h)) := by
  choose a ha using alpha_machine hfeas hall c
  choose w hw using omega_machine hfeas hall c
  have hainj : Function.Injective a := by
    intro h h' hh
    by_contra hne
    refine hfeas.2 _ _ (.inr (c, a h)) (job_ne_idx hne) ⟨?_, ?_⟩ (ha h)
      (by rw [hh]; exact ha h')
    · rw [start_alpha, d_alpha]; have := dl_ge x (c : ℕ) ((h' : ℕ)); omega
    · rw [start_alpha, d_alpha]; have := dl_ge x (c : ℕ) ((h : ℕ)); omega
  have hwinj : Function.Injective w := by
    intro h h' hh
    by_contra hne
    refine hfeas.2 _ _ (.inr (c, w h)) (job_ne_idx hne) ⟨?_, ?_⟩ (hw h)
      (by rw [hh]; exact hw h')
    · rw [start_omega, d_omega]; have := dl_le x (c : ℕ) ((h : ℕ)); omega
    · rw [start_omega, d_omega]; have := dl_le x (c : ℕ) ((h' : ℕ)); omega
  have habij : Function.Bijective a := Finite.injective_iff_bijective.mp hainj
  have hwbij : Function.Bijective w := Finite.injective_iff_bijective.mp hwinj
  set A : Fin 3 ≃ Fin 3 := Equiv.ofBijective a habij with hA
  set W : Fin 3 ≃ Fin 3 := Equiv.ofBijective w hwbij with hW
  set perm : Fin 3 ≃ Fin 3 := A.trans W.symm with hperm
  have hwPerm : ∀ h : Fin 3, w (perm h) = a h := by
    intro h
    have h1 : W (perm h) = A h := by simp [hperm]
    simpa [hA, hW, Equiv.ofBijective_apply] using h1
  have hle : ∀ h : Fin 3, dl x (c : ℕ) ((h : ℕ)) ≤ dl x (c : ℕ) ((perm h : ℕ)) := by
    intro h
    have hsame : σ (.inr (c, perm h, somega)) = some (.inr (c, a h)) := by
      rw [hw (perm h), hwPerm h]
    have hnc : ¬ (inst x).Overlap (jIdx x (.inr (c, h, salpha)))
        (jIdx x (.inr (c, perm h, somega))) :=
      fun hc => hfeas.2 _ _ (.inr (c, a h)) (job_ne_slot (by decide)) hc (ha h) hsame
    have hnc2 := not_ovl_iff.mp hnc
    rw [d_omega, start_alpha, d_alpha, start_omega] at hnc2
    have h1 := dl_ge x (c : ℕ) ((h : ℕ))
    have h2 := dl_even hwf c h
    have h3 := dl_even hwf c (perm h)
    have h4 := dl_ge x (c : ℕ) ((perm h : ℕ))
    omega
  have hsum : (∑ h : Fin 3, dl x (c : ℕ) ((perm h : ℕ))) = ∑ h : Fin 3, dl x (c : ℕ) ((h : ℕ)) :=
    Equiv.sum_comp perm (fun h : Fin 3 => dl x (c : ℕ) ((h : ℕ)))
  have heq : ∀ h : Fin 3, dl x (c : ℕ) ((h : ℕ)) = dl x (c : ℕ) ((perm h : ℕ)) :=
    fun h => (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum.symm h (Finset.mem_univ h)
  have hfix : ∀ h : Fin 3, perm h = h := by
    intro h
    by_contra hne
    exact dl_ne_of_ne hwf (c := c) (Ne.symm hne) (heq h)
  refine ⟨a, habij, fun h => ⟨ha h, ?_⟩⟩
  rw [hw h, ← hwPerm h, hfix h]

/-- The assignment read off a schedule: `v` is true exactly when the variable job of `v`
sits on `v`'s *false* machine. -/
def readAssignment (σ : SchedS x) (v : ℕ) : Bool :=
  decide (∃ u : Fin (nVar x), (u : ℕ) = v ∧ σ (.inl u) = some (.inl (u, false)))

lemma readAssignment_eq {σ' : SchedS x} {v : Fin (nVar x)} {b : Bool}
    (h : σ' (.inl v) = some (.inl (v, b))) : readAssignment σ' (v : ℕ) = !b := by
  cases b
  · simp only [readAssignment, Bool.not_false, decide_eq_true_eq]
    exact ⟨v, rfl, h⟩
  · simp only [readAssignment, Bool.not_true, decide_eq_false_iff_not]
    rintro ⟨u, hu, hσ⟩
    have huv : u = v := Fin.ext hu
    subst huv
    rw [h] at hσ
    simp at hσ

include hfeas hall in
/-- **Lemma 4.** A feasible schedule placing every job yields a satisfying assignment. -/
theorem lemma4 (hwf : WellFormed x) : ∃ τ, Satisfies x τ := by
  refine ⟨readAssignment σ, fun c hc => ?_⟩
  set cF : Fin (nCla x) := ⟨c, hc⟩ with hcF
  obtain ⟨ρ, hρbij, hρ⟩ := observation4 hfeas hall hwf cF
  obtain ⟨h₀, hh₀⟩ := hρbij.2 0
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp (hall (.inr (cF, h₀, slit)))
  have hclause : ∀ t : Fin 3, t ≠ 0 →
      σ (.inr (cF, h₀, slit)) ≠ some (.inr (cF, t)) := by
    intro t ht hct
    obtain ⟨h, hh⟩ := hρbij.2 t
    have hne : h ≠ h₀ := by rintro rfl; exact ht (hh ▸ hh₀ ▸ rfl)
    have hdne := dl_ne_of_ne hwf (c := cF) hne
    have hd1 := dl_ge x (cF : ℕ) ((h : ℕ))
    have hd2 := dl_ge x (cF : ℕ) ((h₀ : ℕ))
    have hd3 := dl_le x (cF : ℕ) ((h : ℕ))
    have hd4 := dl_le x (cF : ℕ) ((h₀ : ℕ))
    rcases Nat.lt_or_ge (dl x (cF : ℕ) ((h₀ : ℕ))) (dl x (cF : ℕ) ((h : ℕ))) with hlt | hge
    · refine hfeas.2 _ _ (.inr (cF, t)) (job_ne_slot (by decide)) ⟨?_, ?_⟩ hct
        (hh ▸ (hρ h).1)
      · rw [start_lit, d_alpha]; omega
      · rw [start_alpha, d_lit]; omega
    · refine hfeas.2 _ _ (.inr (cF, t)) (job_ne_slot (by decide)) ⟨?_, ?_⟩ hct
        (hh ▸ (hρ h).2)
      · rw [start_lit, d_omega]; omega
      · rw [start_omega, d_lit]; omega
  have hvar : σ (.inr (cF, h₀, slit))
      = some (.inl (litVarF hwf cF h₀, litSignB x cF h₀)) := by
    rcases (elig_lit hwf).mp (hfeas.1 _ _ hi) with rfl | rfl | rfl
    · exact absurd hi (hclause 1 (by decide))
    · exact absurd hi (hclause 2 (by decide))
    · exact hi
  obtain ⟨i0, hi0⟩ := Option.ne_none_iff_exists'.mp (hall (.inl (litVarF hwf cF h₀)))
  have hne0 : i0 ≠ .inl (litVarF hwf cF h₀, litSignB x cF h₀) := by
    rintro rfl
    have hd1 := dl_ge x (cF : ℕ) ((h₀ : ℕ))
    have hd2 := dl_le x (cF : ℕ) ((h₀ : ℕ))
    refine hfeas.2 _ _ (.inl (litVarF hwf cF h₀, litSignB x cF h₀)) job_var_ne ⟨?_, ?_⟩ hi0 hvar
    · rw [start_var, d_lit]; omega
    · rw [start_lit, d_var]; omega
  have hfin : σ (.inl (litVarF hwf cF h₀))
      = some (.inl (litVarF hwf cF h₀, !litSignB x cF h₀)) := by
    rcases (elig_var (x := x)).mp (hfeas.1 _ _ hi0) with rfl | rfl
    · cases hp : litSignB x (cF : ℕ) ((h₀ : ℕ))
      · exact hi0
      · exact absurd (by rw [hp]) hne0
    · cases hp : litSignB x (cF : ℕ) ((h₀ : ℕ))
      · exact absurd (by rw [hp]) hne0
      · exact hi0
  refine ⟨(h₀ : ℕ), h₀.isLt, ?_⟩
  have hra := readAssignment_eq hfin
  simp only [Bool.not_not] at hra
  show (litSign x c (h₀ : ℕ) = 1) = (readAssignment σ (litVar x c (h₀ : ℕ)) = true)
  have : readAssignment σ (litVar x c (h₀ : ℕ)) = litSignB x c (h₀ : ℕ) := hra
  rw [this]
  simp [litSignB]

end Lemma4

end Lax470956Proofs.Construction2
