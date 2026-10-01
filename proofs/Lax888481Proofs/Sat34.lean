import Lax888481.SatVariant
import Lax345332.ThreeFourSat

/-!
Tovey's theorem as the statement of another submission: `(3,4)`-SAT of this submission and of
`lax-345332` are the same language, because a variable that does not occur has no occurrences.
-/

namespace Lax888481Proofs.Sat34

open Lax429075.CNF Lax888481.SatVariant Lax434930.PolynomialTime

theorem occ_pos_mem (F : Formula) (i : ℕ) (h : occurrences F i ≠ 0) : i ∈ occurringVars F := by
  unfold occurrences at h
  obtain ⟨l, hl⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero h)
  simp only [List.mem_flatMap, List.mem_filter, beq_iff_eq] at hl
  obtain ⟨C, hC, hlC, hidx⟩ := hl
  unfold occurringVars
  exact List.mem_map.2 ⟨l, List.mem_flatMap.2 ⟨C, hC, hlC⟩, hidx⟩

theorem exact34_iff (F : Formula) : Exact34 F ↔ Lax345332.ThreeFourSat.IsThreeFour F := by
  constructor
  · rintro ⟨h3, h4⟩
    refine ⟨h3, fun i => ?_⟩
    by_cases hi : i ∈ occurringVars F
    · exact h4 i hi
    · have h0 : occurrences F i = 0 := by
        by_contra h
        exact hi (occ_pos_mem F i h)
      show occurrences F i ≤ 4
      omega
  · rintro ⟨h3, h4⟩
    exact ⟨h3, fun i _ => h4 i⟩

theorem sat34_eq : SAT34 = Lax345332.ThreeFourSat.SAT34 := by
  ext w
  constructor
  · rintro ⟨F, hF, h34, hs⟩
    exact ⟨F, hF, (exact34_iff F).1 h34, hs⟩
  · rintro ⟨F, hF, h34, hs⟩
    exact ⟨F, hF, (exact34_iff F).2 h34, hs⟩

/--
---
conclusion: Lax888481.SatVariant.sat34_npHard
---
Tovey's theorem, from the statement of the submission that proves it. That submission's
`(3,4)`-SAT is this one's, so the theorem transfers unchanged.
-/
theorem sat34_npHard :
    ∀ A : Language, A ∈ Lax434930.NondeterministicPolynomialTime.NP →
      Lax429075.Reductions.ManyOne A SAT34 := by
  intro A hA
  rw [sat34_eq]
  exact Lax345332.ThreeFourSat.npHard A hA

end Lax888481Proofs.Sat34
