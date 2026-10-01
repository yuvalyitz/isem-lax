import Lax888481Proofs.Construction2Index

/-!
Construction 2 read in the named language: what each of the four kinds of job occupies,
which machines may run it, and the translation of a schedule between names and numbers.

The three slots of a literal occurrence tile the window `[0, 25)`:
```
   wrapper α : [0, d-1)     literal : [d-1, d)     wrapper ω : [d, 25)
```
and the variable job covers the whole of it, so it overlaps every job of every
occurrence of its variable.
-/

namespace Lax888481Proofs.Construction2

open Lax888481.Scheduling Lax888481.Exact34Encoding Lax888481.Construction2

variable (x : List ℕ)

/-- The slot of the literal job itself. -/
def slit : Fin 3 := 0
/-- The slot of the wrapper before the literal job. -/
def salpha : Fin 3 := 1
/-- The slot of the wrapper after the literal job. -/
def somega : Fin 3 := 2

variable {x}

lemma idx_sub (c h s : ℕ) : nVar x + 9 * c + 3 * h + s - nVar x = 9 * c + 3 * h + s := by
  omega

lemma cOf_eq {c h s : ℕ} (hh : h < 3) (hs : s < 3) : cOf (9 * c + 3 * h + s) = c := by
  simp only [cOf]; omega

lemma hOf_eq {c h s : ℕ} (hh : h < 3) (hs : s < 3) : hOf (9 * c + 3 * h + s) = h := by
  simp only [hOf]; omega

lemma sOf_eq {c h s : ℕ} (hh : h < 3) (hs : s < 3) : sOf (9 * c + 3 * h + s) = s := by
  simp only [sOf]; omega

variable (x)

/-- The processing time, deadline and eligible machines of a clause job, in terms of its
clause, literal and slot. -/
lemma proc_due_elig_cls (c h s : ℕ) (hh : h < 3) (hs : s < 3) :
    procOf x (nVar x + 9 * c + 3 * h + s)
        = (if s = 0 then 1 else if s = 1 then dl x c h - 1 else 25 - dl x c h) ∧
      dueOf x (nVar x + 9 * c + 3 * h + s)
        = (if s = 0 then dl x c h else if s = 1 then dl x c h - 1 else 25) ∧
      eligOf x (nVar x + 9 * c + 3 * h + s)
        = (if s = 0 then
            [2 * nVar x + 3 * c + 1, 2 * nVar x + 3 * c + 2,
              2 * litVar x c h + (if litSign x c h = 1 then 0 else 1)]
          else [2 * nVar x + 3 * c, 2 * nVar x + 3 * c + 1, 2 * nVar x + 3 * c + 2]) := by
  have hnot : ¬ (nVar x + 9 * c + 3 * h + s < nVar x) := by omega
  simp only [procOf, dueOf, eligOf, if_neg hnot, idx_sub, cOf_eq hh hs, hOf_eq hh hs,
    sOf_eq hh hs]
  match s, hs with
  | 0, _ => simp
  | 1, _ => simp
  | 2, _ => simp

lemma procOf_var {v : ℕ} (hv : v < nVar x) : procOf x v = 25 := by
  simp only [procOf, if_pos hv]

lemma dueOf_var {v : ℕ} (hv : v < nVar x) : dueOf x v = 25 := by
  simp only [dueOf, if_pos hv]

lemma eligOf_var {v : ℕ} (hv : v < nVar x) : eligOf x v = [2 * v, 2 * v + 1] := by
  simp only [eligOf, if_pos hv]

/-- A machine is eligible for a job exactly when its number is on the job's list. -/
lemma mem_eligible {j : Fin (nJobs x)} {i : Fin (nMach x)} :
    i ∈ (inst x).eligible j ↔ (i : ℕ) ∈ eligOf x (j : ℕ) :=
  ⟨fun h => (Finset.mem_filter.mp h).2,
   fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

end Lax888481Proofs.Construction2
