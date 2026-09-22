import Lax470956.Construction2

/-!
The word Construction 2 emits, and the proof that it encodes the instance.

The reduction of Theorem 2 is a map on words. `emit` is that map written as a
mathematical function — the blocks of the instance encoding, concatenated — and
`encodesInstance_emit` says it lands where the encoding says it should. The word RAM
program of the reduction is proved to compute `emit`; this file makes that a
statement about scheduling instances rather than about a list of numbers.

The eligibility blocks have two entries for a variable job and three for every clause
job, so the offset array is piecewise linear rather than constant-stride, and the total
length of the target array is `2V + 27C`.
-/

namespace Lax470956Proofs.Emit

open Lax470956.Scheduling Lax470956.InstanceEncoding Lax470956.Construction2

variable (x : List ℕ)

@[simp] lemma procBlock_length : (procBlock x).length = nJobs x := by simp [procBlock]
@[simp] lemma dueBlock_length : (dueBlock x).length = nJobs x := by simp [dueBlock]
@[simp] lemma wtBlock_length : (wtBlock x).length = nJobs x := by simp [wtBlock]
@[simp] lemma offBlock_length : (offBlock x).length = nJobs x + 1 := by simp [offBlock]

/-- Every eligibility block has two entries for a variable job and three otherwise. -/
lemma eligOf_length (j : ℕ) :
    (eligOf x j).length = if j < nVar x then 2 else 3 := by
  unfold eligOf
  split
  · simp
  · dsimp only
    split <;> simp

/-- The target block is as long as the last offset says. -/
lemma tgtBlock_length : (tgtBlock x).length = offOf x (nJobs x) := by
  have key : ∀ N : ℕ, ((List.range N).flatMap (eligOf x)).length
      = 2 * min N (nVar x) + 3 * (N - nVar x) := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, eligOf_length]
      split <;> omega
  rw [tgtBlock, key, offOf]
  unfold nJobs
  split <;> omega

/-! ### Reading the emitted word back

Two rewrites do all the work: stepping past a block whose length is known, and reading
inside the block one has arrived at. Every accessor of the encoding is a chain of the
first followed by one of the second.
-/

/-- Reading past a block reads the rest. -/
lemma getD_skip (A B : List ℕ) (i : ℕ) :
    (A ++ B).getD (A.length + i) 0 = B.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

/-- Reading inside the block one has arrived at. -/
lemma getD_here {A : List ℕ} (B : List ℕ) {i : ℕ} (hi : i < A.length) :
    (A ++ B).getD i 0 = A.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

lemma jobCount_emit : jobCount (emit x) = nJobs x := rfl

lemma machineCount_emit : machineCount (emit x) = nMach x := rfl

lemma emit_length : (emit x).length = 3 + 4 * nJobs x + offOf x (nJobs x) := by
  simp only [emit, List.append_assoc, List.length_append, List.length_cons,
    List.length_nil, procBlock_length, dueBlock_length, wtBlock_length,
    offBlock_length, tgtBlock_length]
  omega

/-- The processing-time block sits right after the two header entries. -/
lemma proc_emit {j : ℕ} (hj : j < nJobs x) : proc (emit x) j = procOf x j := by
  show (emit x).getD (2 + j) 0 = _
  rw [emit]; simp only [List.append_assoc]
  rw [show (2 : ℕ) + j = ([nJobs x, nMach x] : List ℕ).length + j from rfl, getD_skip,
    getD_here _ (by simpa using hj)]
  simp [procBlock, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hj]

/-- The deadline block follows the processing times. -/
lemma due_emit {j : ℕ} (hj : j < nJobs x) : due (emit x) j = dueOf x j := by
  show (emit x).getD (2 + jobCount (emit x) + j) 0 = _
  rw [jobCount_emit, emit]; simp only [List.append_assoc]
  rw [show (2 : ℕ) + nJobs x + j = ([nJobs x, nMach x] : List ℕ).length + (nJobs x + j) by
    simp; omega, getD_skip,
    show nJobs x + j = (procBlock x).length + j by simp, getD_skip,
    getD_here _ (by simpa using hj)]
  simp [dueBlock, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hj]

/-- Every weight in the emitted word is one. -/
lemma wt_emit {j : ℕ} (hj : j < nJobs x) : wt (emit x) j = 1 := by
  show (emit x).getD (2 + 2 * jobCount (emit x) + j) 0 = _
  rw [jobCount_emit, emit]; simp only [List.append_assoc]
  rw [show (2 : ℕ) + 2 * nJobs x + j
      = ([nJobs x, nMach x] : List ℕ).length + (nJobs x + (nJobs x + j)) by simp; omega,
    getD_skip,
    show nJobs x + (nJobs x + j) = (procBlock x).length + (nJobs x + j) by simp, getD_skip,
    show nJobs x + j = (dueBlock x).length + j by simp, getD_skip,
    getD_here _ (by simpa using hj)]
  simp [wtBlock, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hj]

/-- The offset block follows the weights. -/
lemma offset_emit {i : ℕ} (hi : i < nJobs x + 1) : offset (emit x) i = offOf x i := by
  show (emit x).getD (2 + 3 * jobCount (emit x) + i) 0 = _
  rw [jobCount_emit, emit]; simp only [List.append_assoc]
  rw [show (2 : ℕ) + 3 * nJobs x + i
      = ([nJobs x, nMach x] : List ℕ).length + (nJobs x + (nJobs x + (nJobs x + i))) by
        simp; omega, getD_skip,
    show nJobs x + (nJobs x + (nJobs x + i))
      = (procBlock x).length + (nJobs x + (nJobs x + i)) by simp, getD_skip,
    show nJobs x + (nJobs x + i) = (dueBlock x).length + (nJobs x + i) by simp, getD_skip,
    show nJobs x + i = (wtBlock x).length + i by simp, getD_skip,
    getD_here _ (by simpa using hi)]
  simp [offBlock, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hi]

/-- The target block follows the offsets. -/
lemma target_emit {t : ℕ} (ht : t < (tgtBlock x).length) :
    target (emit x) t = (tgtBlock x).getD t 0 := by
  show (emit x).getD (3 + 4 * jobCount (emit x) + t) 0 = _
  rw [jobCount_emit, emit]; simp only [List.append_assoc]
  rw [show (3 : ℕ) + 4 * nJobs x + t
      = ([nJobs x, nMach x] : List ℕ).length
        + (nJobs x + (nJobs x + (nJobs x + ((nJobs x + 1) + t)))) by simp; omega,
    getD_skip,
    show nJobs x + (nJobs x + (nJobs x + ((nJobs x + 1) + t)))
      = (procBlock x).length + (nJobs x + (nJobs x + ((nJobs x + 1) + t))) by simp,
    getD_skip,
    show nJobs x + (nJobs x + ((nJobs x + 1) + t))
      = (dueBlock x).length + (nJobs x + ((nJobs x + 1) + t)) by simp, getD_skip,
    show nJobs x + ((nJobs x + 1) + t) = (wtBlock x).length + ((nJobs x + 1) + t) by simp,
    getD_skip,
    show (nJobs x + 1) + t = (offBlock x).length + t by simp, getD_skip]

/-! ### The eligibility slice

The target block is the eligibility lists of all jobs run together, so reading job `j`'s
block means slicing the flat list between two offsets. The offsets are the
partial lengths, so the slice is the list itself.
-/

/-- The offset of the next job is this one's plus the length of its block. -/
lemma offOf_succ (j : ℕ) :
    offOf x (j + 1) = offOf x j + (if j < nVar x then 2 else 3) := by
  unfold offOf; split_ifs <;> omega

/-- Offsets increase. -/
lemma offOf_mono {a b : ℕ} (h : a ≤ b) : offOf x a ≤ offOf x b := by
  unfold offOf; split_ifs <;> omega

/-- The offsets are the partial lengths of the eligibility lists. -/
lemma flatMap_range_length (N : ℕ) :
    ((List.range N).flatMap (eligOf x)).length = offOf x N := by
  induction N with
  | zero => simp [offOf]
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, eligOf_length]
    rw [offOf_succ]

/-- Reading inside job `j`'s block of the target array reads its eligibility list. -/
lemma tgt_slice {j t : ℕ} (hj : j < nJobs x) (ht : t < (eligOf x j).length) :
    (tgtBlock x).getD (offOf x j + t) 0 = (eligOf x j).getD t 0 := by
  have key : ∀ N, j < N → ((List.range N).flatMap (eligOf x)).getD (offOf x j + t) 0
      = (eligOf x j).getD t 0 := by
    intro N
    induction N with
    | zero => omega
    | succ k ih =>
      intro hjk
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rcases Nat.lt_or_ge j k with h | h
      · rw [getD_here _ ?_]
        · exact ih h
        · rw [flatMap_range_length]
          have h1 := offOf_succ x j
          have h2 := offOf_mono x (show j + 1 ≤ k by omega)
          have h3 := eligOf_length x j
          split_ifs at h1 h3 <;> omega
      · have : j = k := by omega
        subst this
        rw [show offOf x j + t = ((List.range j).flatMap (eligOf x)).length + t by
          rw [flatMap_range_length]]
        exact getD_skip _ _ _
  rw [tgtBlock]
  exact key (nJobs x) hj

/-- Job `j`'s block of the target array lists exactly its eligible machines. -/
lemma mem_eligOf_iff {j : ℕ} (hj : j < nJobs x) (i : ℕ) :
    i ∈ eligOf x j ↔
      ∃ t, offOf x j ≤ t ∧ t < offOf x (j + 1) ∧ (tgtBlock x).getD t 0 = i := by
  have hlen := eligOf_length x j
  have hsucc := offOf_succ x j
  constructor
  · intro hmem
    obtain ⟨t, ht, hget⟩ := List.getElem_of_mem hmem
    refine ⟨offOf x j + t, by omega, by split_ifs at hlen hsucc <;> omega, ?_⟩
    rw [tgt_slice x hj ht, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem ht, Option.getD_some, hget]
  · rintro ⟨t, hlo, hhi, hget⟩
    have ht' : t - offOf x j < (eligOf x j).length := by
      split_ifs at hlen hsucc <;> omega
    rw [show t = offOf x j + (t - offOf x j) by omega, tgt_slice x hj ht',
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some] at hget
    exact hget ▸ List.getElem_mem ht'

/-! ### The emitted word encodes the constructed instance -/

open Lax470956.Exact34Encoding in
/-- On a well-formed formula every machine number the construction emits is a machine of
the instance. This is the one place well-formedness is needed: the machine of a literal
job is read off the variable the literal mentions, and a word that mentions a variable
out of range would name a machine that does not exist. -/
lemma eligOf_lt (hwf : WellFormed x) {j : ℕ} (hj : j < nJobs x) :
    ∀ i ∈ eligOf x j, i < nMach x := by
  intro i hi
  unfold eligOf at hi
  split at hi
  · rename_i hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold nMach; omega
  · rename_i hge
    have hi9 : j - nVar x < 9 * nCla x := by unfold nJobs at hj; omega
    have hc : cOf (j - nVar x) < nCla x := by
      unfold cOf; rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    have hh : hOf (j - nVar x) < 3 := by
      unfold hOf
      have h9 : (j - nVar x) % 9 < 9 := Nat.mod_lt _ (by omega)
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    dsimp only at hi
    split at hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have hv : litVar x (cOf (j - nVar x)) (hOf (j - nVar x)) < nVar x :=
        hwf.var_lt _ hc _ hh
      unfold nMach
      rcases hi with rfl | rfl | rfl
      · omega
      · omega
      · split <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      unfold nMach
      rcases hi with rfl | rfl | rfl <;> omega

open Lax470956.Exact34Encoding in
/-- **The emitted word encodes the constructed instance.** -/
theorem encodesInstance_emit (hwf : WellFormed x) :
    EncodesInstance (emit x) (inst x) where
  jobCount_eq := jobCount_emit x
  machineCount_eq := machineCount_emit x
  length_eq := by
    rw [emit_length, inst_jobs, offset_emit x (Nat.lt_succ_self _)]
  proc_eq j := proc_emit x j.isLt
  due_eq j := due_emit x j.isLt
  wt_eq j := by rw [wt_emit x j.isLt]; rfl
  offset_zero := by rw [offset_emit x (Nat.succ_pos _)]; simp [offOf]
  offset_mono j hj := by
    rw [inst_jobs] at hj
    rw [offset_emit x (by omega), offset_emit x (by omega)]
    exact offOf_mono x (Nat.le_succ _)
  target_lt t ht := by
    rw [inst_jobs, offset_emit x (Nat.lt_succ_self _)] at ht
    have htl : t < (tgtBlock x).length := by rw [tgtBlock, flatMap_range_length]; exact ht
    rw [target_emit x htl]
    have hmem : (tgtBlock x).getD t 0 ∈ tgtBlock x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
      exact List.getElem_mem _
    have hmem' : (tgtBlock x).getD t 0 ∈ (List.range (nJobs x)).flatMap (eligOf x) := hmem
    rw [List.mem_flatMap] at hmem'
    obtain ⟨j, hjr, hj⟩ := hmem'
    exact eligOf_lt x hwf (List.mem_range.mp hjr) _ hj
  eligible_iff j i := by
    have hj : (j : ℕ) < nJobs x := j.isLt
    have hfilter : i ∈ (inst x).eligible j ↔ (i : ℕ) ∈ eligOf x (j : ℕ) :=
      ⟨fun h => (Finset.mem_filter.mp h).2,
       fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
    rw [hfilter, mem_eligOf_iff x hj (i : ℕ)]
    constructor
    · rintro ⟨t, hlo, hhi, hget⟩
      have hlt : t < (tgtBlock x).length := by
        rw [tgtBlock, flatMap_range_length]
        exact lt_of_lt_of_le hhi (offOf_mono x (by omega))
      exact ⟨t, by rw [offset_emit x (by omega)]; exact hlo,
        by rw [offset_emit x (by omega)]; exact hhi,
        by rw [target_emit x hlt]; exact hget⟩
    · rintro ⟨t, hlo, hhi, hget⟩
      rw [offset_emit x (by omega)] at hlo
      rw [offset_emit x (by omega)] at hhi
      have hlt : t < (tgtBlock x).length := by
        rw [tgtBlock, flatMap_range_length]
        exact lt_of_lt_of_le hhi (offOf_mono x (by omega))
      exact ⟨t, hlo, hhi, by rw [← target_emit x hlt]; exact hget⟩

open Lax470956.Exact34Encoding in
/--
---
conclusion: Lax470956.Construction2.emit_encodes
---
Each accessor of the encoding reads the block it names: two rewrites do all the work,
one stepping past a block whose length is known and one reading inside the block
arrived at. The last field, that a job's block of the target array lists exactly its
eligible machines, is the flat-map slice between consecutive offsets.
-/
theorem emit_encodes (x : List ℕ) (hwf : WellFormed x) :
    EncodesInstance (emit x) (inst x) := encodesInstance_emit x hwf

end Lax470956Proofs.Emit
