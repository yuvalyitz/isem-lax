import Lax470956Proofs.Construction2Named
import Mathlib.Logic.Equiv.Basic

/-!
Schedules of Construction 2 in the named language, and the translation to and from the
numbered schedules the instance is stated with.
-/

namespace Lax470956Proofs.Construction2

open Lax470956.Scheduling Lax470956.Exact34Encoding Lax470956.Construction2

variable {x : List ℕ}

/-- A schedule of the construction, named. -/
abbrev SchedS (x : List ℕ) : Type := JobS x → Option (MachS x)

/-- Feasibility, named: every placed job sits on an eligible machine, and no two
overlapping jobs share one. -/
def FeasibleS (σ : SchedS x) : Prop :=
  (∀ a i, σ a = some i → mIdx x i ∈ (inst x).eligible (jIdx x a)) ∧
  (∀ a a' i, a ≠ a' → (inst x).Overlap (jIdx x a) (jIdx x a') → σ a = some i → σ a' ≠ some i)

private lemma map_eq_some_iff {α β : Type} {f : α → β} {o : Option α} {b : β} :
    o.map f = some b ↔ ∃ a, o = some a ∧ f a = b := by cases o <;> simp

private lemma map_eq_none_iff {α β : Type} {f : α → β} {o : Option α} :
    o.map f = none ↔ o = none := by cases o <;> simp

lemma jIdx_symm (j : Fin (nJobs x)) : jIdx x ((jobEquiv x).symm j) = j :=
  (jobEquiv x).apply_symm_apply j

lemma mIdx_symm (i : Fin (nMach x)) : mIdx x ((machEquiv x).symm i) = i :=
  (machEquiv x).apply_symm_apply i

/-- A named feasible schedule placing every job gives a numbered one. -/
theorem allSchedulable_of_named {σ : SchedS x} (hf : FeasibleS σ) (hall : ∀ a, σ a ≠ none) :
    (inst x).AllSchedulable := by
  refine ⟨fun j => (σ ((jobEquiv x).symm j)).map (mIdx x), ⟨?_, ?_⟩, ?_⟩
  · intro j i hji
    have hj1 : jIdx x ((jobEquiv x).symm j) = j := jIdx_symm j
    obtain ⟨i₀, h₀, rfl⟩ := map_eq_some_iff.mp hji
    have hmem := hf.1 _ _ h₀
    rwa [hj1] at hmem
  · intro j j' i hne hov hj hj'
    obtain ⟨i₀, h₀, hm₀⟩ := map_eq_some_iff.mp hj
    obtain ⟨i₁, h₁, hm₁⟩ := map_eq_some_iff.mp hj'
    have hii : i₀ = i₁ := mIdx_injective x (hm₀.trans hm₁.symm)
    subst hii
    have hj1 : jIdx x ((jobEquiv x).symm j) = j := jIdx_symm j
    have hj2 : jIdx x ((jobEquiv x).symm j') = j' := jIdx_symm j'
    refine hf.2 ((jobEquiv x).symm j) ((jobEquiv x).symm j') i₀ ?_ ?_ h₀ h₁
    · exact fun hc => hne (by rw [← hj1, ← hj2, hc])
    · rwa [hj1, hj2]
  · exact fun j hc => hall _ (map_eq_none_iff.mp hc)

/-- A numbered feasible schedule placing every job gives a named one. -/
theorem named_of_allSchedulable (h : (inst x).AllSchedulable) :
    ∃ σ : SchedS x, FeasibleS σ ∧ ∀ a, σ a ≠ none := by
  obtain ⟨σ', hfeas, hall⟩ := h
  refine ⟨fun a => (σ' (jIdx x a)).map (machEquiv x).symm, ⟨?_, ?_⟩, ?_⟩
  · intro a i hai
    obtain ⟨i₀, h₀, rfl⟩ := map_eq_some_iff.mp hai
    rw [mIdx_symm]
    exact hfeas.1 _ _ h₀
  · intro a a' i hne hov hj hj'
    obtain ⟨i₀, h₀, hm₀⟩ := map_eq_some_iff.mp hj
    obtain ⟨i₁, h₁, hm₁⟩ := map_eq_some_iff.mp hj'
    have hii : i₀ = i₁ := by
      have := hm₀.trans hm₁.symm
      exact (machEquiv x).symm.injective this
    subst hii
    exact hfeas.2 _ _ i₀ (fun hc => hne (jIdx_injective x hc)) hov h₀ h₁
  · exact fun a hc => hall _ (map_eq_none_iff.mp hc)

end Lax470956Proofs.Construction2
