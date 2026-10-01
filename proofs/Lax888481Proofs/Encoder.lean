import Lax888481.InstanceEncoding

/-!
Writing an instance out as a word, once and for all.

`InstanceEncoding` lays a word out in six blocks: the two counts, one entry per job for
each of the processing times, the deadlines and the weights, then `n + 1` offsets and the
eligible machines of every job run together. That layout does not depend on which
construction produced the instance, and neither does the argument that a word built this
way encodes it. This file does both generically, from nothing but the accessors.

A construction supplies a `Blocks`: how many jobs and machines, and the four accessors as
functions on job numbers. `encodesInstance` then asks only what concerns the
construction: that the accessors agree with the instance, and that the machine numbers
it lists are machines.
-/

namespace Lax888481Proofs.Encoder

open Lax888481.Scheduling Lax888481.InstanceEncoding

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An instance presented by its accessors on job numbers. -/
structure Blocks where
  /-- The number of jobs. -/
  jobs : ℕ
  /-- The number of machines. -/
  machines : ℕ
  /-- The processing time of each job. -/
  p : ℕ → ℕ
  /-- The deadline of each job. -/
  d : ℕ → ℕ
  /-- The weight of each job. -/
  w : ℕ → ℕ
  /-- The eligible machines of each job, as a list of machine numbers. -/
  elig : ℕ → List ℕ

variable (S : Blocks)

/-- Where job `j`'s block of the target array begins: the total length of the earlier
eligibility lists. -/
def offOf (j : ℕ) : ℕ := ((List.range j).map fun i => (S.elig i).length).sum

/-- The processing-time block. -/
def procBlock : List ℕ := (List.range S.jobs).map S.p

/-- The deadline block. -/
def dueBlock : List ℕ := (List.range S.jobs).map S.d

/-- The weight block. -/
def wtBlock : List ℕ := (List.range S.jobs).map S.w

/-- The offset block, one entry per job and one more. -/
def offBlock : List ℕ := (List.range (S.jobs + 1)).map (offOf S)

/-- The target block: the eligible machines of each job in turn. -/
def tgtBlock : List ℕ := (List.range S.jobs).flatMap S.elig

/-- **The word.** -/
def emit : List ℕ :=
  [S.jobs, S.machines] ++ procBlock S ++ dueBlock S ++ wtBlock S ++ offBlock S ++ tgtBlock S

@[simp] lemma procBlock_length : (procBlock S).length = S.jobs := by simp [procBlock]
@[simp] lemma dueBlock_length : (dueBlock S).length = S.jobs := by simp [dueBlock]
@[simp] lemma wtBlock_length : (wtBlock S).length = S.jobs := by simp [wtBlock]
@[simp] lemma offBlock_length : (offBlock S).length = S.jobs + 1 := by simp [offBlock]

lemma offOf_succ (j : ℕ) : offOf S (j + 1) = offOf S j + (S.elig j).length := by
  simp [offOf, List.range_succ]

lemma offOf_mono {a b : ℕ} (h : a ≤ b) : offOf S a ≤ offOf S b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    exact le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge a (k + 1) with hk | hk
    · have h1 := ih (by omega)
      rw [offOf_succ]
      omega
    · have ha : a = k + 1 := by omega
      subst ha
      exact le_refl _

lemma flatMap_range_length (N : ℕ) : ((List.range N).flatMap S.elig).length = offOf S N := by
  induction N with
  | zero => simp [offOf]
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [offOf_succ]

@[simp] lemma tgtBlock_length : (tgtBlock S).length = offOf S S.jobs :=
  flatMap_range_length S S.jobs

/-! ### Reading the Word -/

lemma getD_skip (A B : List ℕ) (i : ℕ) :
    (A ++ B).getD (A.length + i) 0 = B.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

lemma getD_here {A : List ℕ} (B : List ℕ) {i : ℕ} (hi : i < A.length) :
    (A ++ B).getD i 0 = A.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

@[simp] lemma jobCount_emit : jobCount (emit S) = S.jobs := rfl
@[simp] lemma machineCount_emit : machineCount (emit S) = S.machines := rfl

lemma emit_length : (emit S).length = 3 + 4 * S.jobs + offOf S S.jobs := by
  simp only [emit, List.append_assoc, List.length_append, List.length_cons,
    List.length_nil, procBlock_length, dueBlock_length, wtBlock_length,
    offBlock_length, tgtBlock_length]
  omega

lemma proc_emit {j : ℕ} (hj : j < S.jobs) : proc (emit S) j = S.p j := by
  show (emit S).getD (2 + j) 0 = _
  rw [emit]; simp only [List.append_assoc]
  rw [show (2 : ℕ) + j = ([S.jobs, S.machines] : List ℕ).length + j from rfl, getD_skip,
    getD_here _ (by simpa using hj)]
  simp [procBlock, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hj]

lemma due_emit {j : ℕ} (hj : j < S.jobs) : due (emit S) j = S.d j := by
  show (emit S).getD (2 + jobCount (emit S) + j) 0 = _
  rw [jobCount_emit, emit]; simp only [List.append_assoc]
  rw [show (2 : ℕ) + S.jobs + j = ([S.jobs, S.machines] : List ℕ).length + (S.jobs + j) by
    simp; omega, getD_skip,
    show S.jobs + j = (procBlock S).length + j by simp, getD_skip,
    getD_here _ (by simpa using hj)]
  simp [dueBlock, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hj]

lemma wt_emit {j : ℕ} (hj : j < S.jobs) : wt (emit S) j = S.w j := by
  show (emit S).getD (2 + 2 * jobCount (emit S) + j) 0 = _
  rw [jobCount_emit, emit]; simp only [List.append_assoc]
  rw [show (2 : ℕ) + 2 * S.jobs + j
      = ([S.jobs, S.machines] : List ℕ).length + (S.jobs + (S.jobs + j)) by simp; omega,
    getD_skip,
    show S.jobs + (S.jobs + j) = (procBlock S).length + (S.jobs + j) by simp, getD_skip,
    show S.jobs + j = (dueBlock S).length + j by simp, getD_skip,
    getD_here _ (by simpa using hj)]
  simp [wtBlock, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hj]

lemma offset_emit {i : ℕ} (hi : i < S.jobs + 1) : offset (emit S) i = offOf S i := by
  show (emit S).getD (2 + 3 * jobCount (emit S) + i) 0 = _
  rw [jobCount_emit, emit]; simp only [List.append_assoc]
  rw [show (2 : ℕ) + 3 * S.jobs + i
      = ([S.jobs, S.machines] : List ℕ).length + (S.jobs + (S.jobs + (S.jobs + i))) by
        simp; omega, getD_skip,
    show S.jobs + (S.jobs + (S.jobs + i)) = (procBlock S).length + (S.jobs + (S.jobs + i)) by
      simp, getD_skip,
    show S.jobs + (S.jobs + i) = (dueBlock S).length + (S.jobs + i) by simp, getD_skip,
    show S.jobs + i = (wtBlock S).length + i by simp, getD_skip,
    getD_here _ (by simpa using hi)]
  simp [offBlock, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hi]

lemma target_emit {t : ℕ} : target (emit S) t = (tgtBlock S).getD t 0 := by
  show (emit S).getD (3 + 4 * jobCount (emit S) + t) 0 = _
  rw [jobCount_emit, emit]; simp only [List.append_assoc]
  rw [show (3 : ℕ) + 4 * S.jobs + t
      = ([S.jobs, S.machines] : List ℕ).length
        + (S.jobs + (S.jobs + (S.jobs + ((S.jobs + 1) + t)))) by simp; omega,
    getD_skip,
    show S.jobs + (S.jobs + (S.jobs + ((S.jobs + 1) + t)))
      = (procBlock S).length + (S.jobs + (S.jobs + ((S.jobs + 1) + t))) by simp,
    getD_skip,
    show S.jobs + (S.jobs + ((S.jobs + 1) + t))
      = (dueBlock S).length + (S.jobs + ((S.jobs + 1) + t)) by simp, getD_skip,
    show S.jobs + ((S.jobs + 1) + t) = (wtBlock S).length + ((S.jobs + 1) + t) by simp,
    getD_skip,
    show (S.jobs + 1) + t = (offBlock S).length + t by simp, getD_skip]

/-! ### The Eligibility Slice -/

lemma tgt_slice {j t : ℕ} (hj : j < S.jobs) (ht : t < (S.elig j).length) :
    (tgtBlock S).getD (offOf S j + t) 0 = (S.elig j).getD t 0 := by
  have key : ∀ N, j < N → ((List.range N).flatMap S.elig).getD (offOf S j + t) 0
      = (S.elig j).getD t 0 := by
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
          have h1 := offOf_succ S j
          have h2 := offOf_mono S (show j + 1 ≤ k by omega)
          omega
      · have hjk' : j = k := by omega
        subst hjk'
        rw [show offOf S j + t = ((List.range j).flatMap S.elig).length + t by
          rw [flatMap_range_length]]
        exact getD_skip _ _ _
  rw [tgtBlock]
  exact key S.jobs hj

lemma mem_elig_iff {j : ℕ} (hj : j < S.jobs) (i : ℕ) :
    i ∈ S.elig j ↔
      ∃ t, offOf S j ≤ t ∧ t < offOf S (j + 1) ∧ (tgtBlock S).getD t 0 = i := by
  have hsucc := offOf_succ S j
  constructor
  · intro hmem
    obtain ⟨t, ht, hget⟩ := List.getElem_of_mem hmem
    refine ⟨offOf S j + t, by omega, by omega, ?_⟩
    rw [tgt_slice S hj ht, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem ht, Option.getD_some, hget]
  · rintro ⟨t, hlo, hhi, hget⟩
    have ht' : t - offOf S j < (S.elig j).length := by omega
    rw [show t = offOf S j + (t - offOf S j) by omega, tgt_slice S hj ht',
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some] at hget
    exact hget ▸ List.getElem_mem ht'

/-! ### The Word Encodes the Instance -/

/-- **A word built from an instance's accessors encodes it.** -/
theorem encodesInstance (I : Instance)
    (hj : S.jobs = I.jobs) (hm : S.machines = I.machines)
    (hp : ∀ j : Fin I.jobs, S.p j = I.p j)
    (hd : ∀ j : Fin I.jobs, S.d j = I.d j)
    (hw : ∀ j : Fin I.jobs, S.w j = I.w j)
    (hlt : ∀ j < S.jobs, ∀ v ∈ S.elig j, v < S.machines)
    (helig : ∀ (j : Fin I.jobs) (i : Fin I.machines), i ∈ I.eligible j ↔ (i : ℕ) ∈ S.elig j) :
    EncodesInstance (emit S) I where
  jobCount_eq := by rw [jobCount_emit, hj]
  machineCount_eq := by rw [machineCount_emit, hm]
  length_eq := by
    rw [emit_length, offset_emit S (by omega), hj]
  proc_eq := fun j => by
    rw [proc_emit S (by rw [hj]; exact j.isLt)]; exact hp j
  due_eq := fun j => by
    rw [due_emit S (by rw [hj]; exact j.isLt)]; exact hd j
  wt_eq := fun j => by
    rw [wt_emit S (by rw [hj]; exact j.isLt)]; exact hw j
  offset_zero := by rw [offset_emit S (by omega)]; simp [offOf]
  offset_mono := fun j hjj => by
    rw [offset_emit S (by omega), offset_emit S (by omega)]
    exact offOf_mono S (by omega)
  target_lt := fun t ht => by
    rw [offset_emit S (by omega)] at ht
    rw [target_emit, ← hm]
    have htl : t < (tgtBlock S).length := by rw [tgtBlock_length, hj]; exact ht
    have hmem : (tgtBlock S).getD t 0 ∈ tgtBlock S := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
      exact List.getElem_mem htl
    rw [tgtBlock, List.mem_flatMap] at hmem
    obtain ⟨a, ha, hva⟩ := hmem
    exact hlt a (List.mem_range.mp ha) _ hva
  eligible_iff := fun j i => by
    rw [helig j i, mem_elig_iff S (by rw [hj]; exact j.isLt)]
    constructor
    · rintro ⟨t, h1, h2, h3⟩
      exact ⟨t, by rw [offset_emit S (by omega)]; exact h1,
        by rw [offset_emit S (by omega)]; exact h2, by rw [target_emit]; exact h3⟩
    · rintro ⟨t, h1, h2, h3⟩
      rw [offset_emit S (by omega)] at h1
      rw [offset_emit S (by omega)] at h2
      rw [target_emit] at h3
      exact ⟨t, h1, h2, h3⟩

end Lax888481Proofs.Encoder
