import Lax470956Proofs.SweepBody
import Lax470956.SchedulingProblems

/-!
The sweep's pre-passes: the largest processing time, the powers that index the table,
the jobs of each deadline, and the block starts.
-/

namespace Lax470956Proofs.SweepPre

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.Scheduling Lax470956.Scheduling.Instance
open Lax470956.InstanceEncoding Lax470956.SchedulingProblems
open Lax470956Proofs.SweepProg Lax470956Proofs.SweepTable Lax470956Proofs.SweepBody

variable {B : ℕ} {x : List ℕ} {n : ℕ}

/-! ### The Largest Processing Time -/

/-- The largest of the first `N` processing times. -/
def pmaxAux (x : List ℕ) (N : ℕ) : ℕ := ((List.range N).map (proc x)).foldr max 0

lemma foldr_max_append (l1 l2 : List ℕ) :
    (l1 ++ l2).foldr max 0 = max (l1.foldr max 0) (l2.foldr max 0) := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp [ih, max_assoc]

lemma pmaxAux_succ (x : List ℕ) (N : ℕ) :
    pmaxAux x (N + 1) = max (pmaxAux x N) (proc x N) := by
  unfold pmaxAux
  rw [List.range_succ, List.map_append, foldr_max_append]
  simp

lemma pmaxAux_ge (x : List ℕ) : ∀ N, ∀ j < N, proc x j ≤ pmaxAux x N := by
  intro N
  induction N with
  | zero => intro j hj; omega
  | succ N ih =>
      intro j hj
      rw [pmaxAux_succ]
      rcases Nat.lt_or_ge j N with h | h
      · exact le_trans (ih j h) (le_max_left _ _)
      · rw [show j = N from by omega]; exact le_max_right _ _

lemma pmaxAux_lt {B : ℕ} (hxg : ∀ i, x.getD i 0 + 2 < B) (hB : 2 < B) :
    ∀ N, pmaxAux x N + 2 < B := by
  intro N
  induction N with
  | zero => simpa [pmaxAux] using hB
  | succ N ih =>
      rw [pmaxAux_succ]
      have := hxg (2 + N)
      simp only [proc]
      omega

lemma pmaxAux_jobCount (x : List ℕ) : pmaxAux x (jobCount x) = pmaxOf x := rfl

/-- The state of the largest-processing-time pass. -/
def PInv (x : List ℕ) (n : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "n" = n ∧ σ.vars "j" ≤ n ∧ σ.vars "P" = pmaxAux x (σ.vars "j")

theorem pmaxBody_spec (hxg : ∀ i, x.getD i 0 + 2 < B) (hB : 2 < B)
    (hnB : n + 2 < B) (hlen : 2 + n ≤ x.length) :
    Spec B (fun σ => PInv x n σ ∧ σ.vars "j" < n) pmaxBody
      (fun σ σ' => PInv x n σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 15 := by
  run_vcg
  all_goals obtain ⟨ha, hn, hj, hP⟩ := ‹PInv x n σ›
  all_goals have hjlt : σ.vars "j" < n := ‹σ.vars "j" < n›
  all_goals have haL : (σ.arrs "a").length = x.length := (by rw [ha])
  all_goals have hval : (σ.arrs "a").getD (2 + σ.vars "j") 0 = proc x (σ.vars "j") :=
    (by rw [ha]; rfl)
  all_goals have hvB : proc x (σ.vars "j") + 2 < B := hxg _
  all_goals have hPB : σ.vars "P" + 2 < B := (by rw [hP]; exact pmaxAux_lt hxg hB _)
  all_goals simp only [PInv, Env.setVar, String.reduceEq, ↓reduceIte, if_pos rfl, hval] at *
  all_goals try omega
  refine ⟨⟨ha, hn, by omega, ?_⟩, by omega⟩
  rw [pmaxAux_succ, hP, nat_mx]

theorem pmaxLoop_spec (hxg : ∀ i, x.getD i 0 + 2 < B) (hB : 2 < B)
    (hnB : n + 2 < B) (hlen : 2 + n ≤ x.length) (hjc : jobCount x = n) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "n" = n) pmaxLoop
      (fun _ σ' => σ'.arrs "a" = x ∧ σ'.vars "n" = n ∧ σ'.vars "P" = pmaxOf x ∧
        σ'.vars "j" = n) (19 * n + 8) := by
  intro σ ⟨ha, hn⟩
  obtain ⟨σ', hrun, ⟨ha', hn', -, hP'⟩, hj'⟩ :=
    (Spec.forRangeZero (B := B) "j" "n" (PInv x n) n 15 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.2.1)
      (pmaxBody_spec hxg hB hnB hlen)) (σ.setVar "P" 0)
      ⟨by simp [Env.setVar, ha], by simp [Env.setVar, hn], by simp [Env.setVar],
        by simp [Env.setVar, pmaxAux]⟩
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (SweepBody.evalB_lit (by omega))) hrun).mono
    (by norm_num [Expr.size]; omega), ha', hn', ?_, hj'⟩
  rw [hP', hj', ← hjc]
  exact pmaxAux_jobCount x

/-! ### The Powers That Index the Table -/

/-- The state of the powers pass. -/
def QInv (m P : ℕ) (σ : Env) : Prop :=
  σ.vars "m" = m ∧ σ.vars "P" = P ∧ σ.vars "i" ≤ m ∧
    σ.vars "S" = (P + 1) ^ (σ.vars "i") ∧ m ≤ (σ.arrs "pw").length ∧
    ∀ i, i < σ.vars "i" → (σ.arrs "pw").getD i 0 = (P + 1) ^ i

variable {m P : ℕ}

lemma pow_le_pow_of_le {P a b : ℕ} (h : a ≤ b) : (P + 1) ^ a ≤ (P + 1) ^ b :=
  Nat.pow_le_pow_right (by omega) h

theorem powBody_spec (hSB : (P + 1) ^ m + 2 < B) (hmB : m + 2 < B) (hPB : P + 2 < B) :
    Spec B (fun σ => QInv m P σ ∧ σ.vars "i" < m) powBody
      (fun σ σ' => QInv m P σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 13 := by
  run_vcg
  all_goals obtain ⟨hm, hP, hi, hS, hlen, hcell⟩ := ‹QInv m P σ›
  all_goals have hilt : σ.vars "i" < m := ‹σ.vars "i" < m›
  all_goals have hSle : σ.vars "S" ≤ (P + 1) ^ m :=
    (by rw [hS]; exact pow_le_pow_of_le (by omega))
  all_goals have hSnext : σ.vars "S" * (σ.vars "P" + 1) ≤ (P + 1) ^ m :=
    (by rw [hS, hP, ← pow_succ]; exact pow_le_pow_of_le (by omega))
  all_goals try simp only [QInv, Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte,
    if_pos rfl, List.length_set]
  all_goals try omega
  all_goals try (rw [hP]; omega)
  refine ⟨⟨hm, hP, by omega, ?_, hlen, ?_⟩, trivial⟩
  · rw [hS, hP, ← pow_succ]
  · intro i hilt2
    by_cases hii : i = σ.vars "i"
    · subst hii; rw [getD_set_self (by omega), hS]
    · rw [getD_set_other hii]; exact hcell i (by omega)

theorem powLoop_spec (hSB : (P + 1) ^ m + 2 < B) (hmB : m + 2 < B) (hPB : P + 2 < B) :
    Spec B (fun σ => σ.vars "m" = m ∧ σ.vars "P" = P ∧ m ≤ (σ.arrs "pw").length) powLoop
      (fun _ σ' => σ'.vars "m" = m ∧ σ'.vars "P" = P ∧ σ'.vars "S" = (P + 1) ^ m ∧
        Pw m P σ' ∧ σ'.vars "i" = m) (17 * m + 8) := by
  intro σ ⟨hm, hP, hlen⟩
  obtain ⟨σ', hrun, ⟨hm', hP', -, hS', hlen', hcell'⟩, hi'⟩ :=
    (Spec.forRangeZero (B := B) "i" "m" (QInv m P) m 13 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.1)
      (powBody_spec hSB hmB hPB)) (σ.setVar "S" 1)
      ⟨by simp [Env.setVar, hm], by simp [Env.setVar, hP], by simp [Env.setVar],
        by simp [Env.setVar], by simp [Env.setVar, hlen], by simp [Env.setVar]⟩
  refine ⟨σ', (Run.seq (Run.assign (v := 1) (SweepBody.evalB_lit (by omega))) hrun).mono
    (by norm_num [Expr.size]; omega), hm', hP', by rw [hS', hi'], ⟨hlen', ?_⟩, hi'⟩
  intro i hi
  exact hcell' i (by omega)

/-! ### The Jobs of Each Deadline -/

/-- The jobs among the first `N` whose deadline is `d`, the most recent first. -/
def jlist (f : ℕ → ℕ) (d : ℕ) : ℕ → List ℕ
  | 0 => []
  | N + 1 => if f N = d then N :: jlist f d N else jlist f d N

/-- One more than the head of a list, or zero. -/
def hd1 : List ℕ → ℕ
  | [] => 0
  | a :: _ => a + 1

lemma jlist_succ_pos {f : ℕ → ℕ} {d N : ℕ} (h : f N = d) :
    jlist f d (N + 1) = N :: jlist f d N := by rw [jlist, if_pos h]

lemma jlist_succ_neg {f : ℕ → ℕ} {d N : ℕ} (h : f N ≠ d) :
    jlist f d (N + 1) = jlist f d N := by rw [jlist, if_neg h]

lemma jlist_lt (f : ℕ → ℕ) (d : ℕ) : ∀ N, ∀ j ∈ jlist f d N, j < N := by
  intro N
  induction N with
  | zero => intro j hj; simp [jlist] at hj
  | succ N ih =>
      intro j hj
      rw [jlist] at hj
      split at hj
      · rcases List.mem_cons.mp hj with rfl | hj'
        · omega
        · have := ih j hj'; omega
      · have := ih j hj; omega

lemma hd1_le (f : ℕ → ℕ) (d N : ℕ) : hd1 (jlist f d N) ≤ N := by
  rcases hl : jlist f d N with _ | ⟨a, l⟩
  · simp [hd1]
  · have := jlist_lt f d N a (by rw [hl]; exact List.mem_cons_self)
    simp only [hd1]; omega

lemma jlist_mem (f : ℕ → ℕ) (d : ℕ) : ∀ N, ∀ j, j ∈ jlist f d N ↔ j < N ∧ f j = d := by
  intro N
  induction N with
  | zero => intro j; simp [jlist]
  | succ N ih =>
      intro j
      rw [jlist]
      split
      · rename_i h
        simp only [List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨by omega, h⟩
          · exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge j N with hlt | hge
          · exact Or.inr ⟨hlt, h2⟩
          · exact Or.inl (by omega)
      · rename_i h
        rw [ih]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rcases Nat.lt_or_ge j N with hlt | hge
          · exact hlt
          · exact absurd (by rw [show j = N from by omega] at h2; exact h2) h

/-- The state of the bucketing pass. -/
def BkInv (x : List ℕ) (n Lo : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "n" = n ∧ σ.vars "j" ≤ n ∧
    Lo ≤ (σ.arrs "occ").length ∧ Lo ≤ (σ.arrs "fj").length ∧ n ≤ (σ.arrs "nj").length ∧
    (∀ d, (σ.arrs "fj").getD d 0 = hd1 (jlist (due x) d (σ.vars "j"))) ∧
    (∀ d, (σ.arrs "occ").getD d 0 = if jlist (due x) d (σ.vars "j") = [] then 0 else 1) ∧
    (∀ j, j < σ.vars "j" → (σ.arrs "nj").getD j 0 = hd1 (jlist (due x) (due x j) j))

theorem bucketBody_spec (Lo : ℕ) (hxg : ∀ i, x.getD i 0 + 2 < B) (hB : 2 < B)
    (hnB : n + 2 < B) (hxB : x.length + 2 < B) (hlen : 2 + n + n ≤ x.length)
    (hjc : jobCount x = n)
    (hdue : ∀ j, j < n → due x j < Lo) :
    Spec B (fun σ => BkInv x n Lo σ ∧ σ.vars "j" < n) bucketBody
      (fun σ σ' => BkInv x n Lo σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 23 := by
  run_vcg
  all_goals obtain ⟨ha, hn, hj, hoL, hfL, hnL, hfj, hocc, hnj⟩ := ‹BkInv x n Lo σ›
  all_goals have hjlt : σ.vars "j" < n := ‹σ.vars "j" < n›
  all_goals have haL : (σ.arrs "a").length = x.length := (by rw [ha])
  all_goals have hval : (σ.arrs "a").getD (2 + σ.vars "n" + σ.vars "j") 0 = due x (σ.vars "j") := (by rw [ha, hn, due, hjc])
  all_goals have hvB : due x (σ.vars "j") + 2 < B := hxg _
  all_goals have hdlt : due x (σ.vars "j") < Lo := hdue _ hjlt
  all_goals have hfjB : (σ.arrs "fj").getD (due x (σ.vars "j")) 0 ≤ n := (by rw [hfj]; exact le_trans (hd1_le _ _ _) hj)
  all_goals try simp only [BkInv, Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte,
    if_pos rfl, List.length_set, hval]
  all_goals try omega
  refine ⟨⟨ha, hn, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩, trivial⟩
  · intro d
    by_cases hd : d = due x (σ.vars "j")
    · subst hd
      rw [getD_set_self (by omega), jlist_succ_pos rfl]
      rfl
    · rw [getD_set_other hd, hfj, jlist_succ_neg (by exact fun hc => hd hc.symm)]
  · intro d
    by_cases hd : d = due x (σ.vars "j")
    · subst hd
      rw [getD_set_self (by omega), jlist_succ_pos rfl]
      simp
    · rw [getD_set_other hd, hocc, jlist_succ_neg (by exact fun hc => hd hc.symm)]
  · intro j hjj
    by_cases hjeq : j = σ.vars "j"
    · subst hjeq
      rw [getD_set_self (by omega), hfj]
    · rw [getD_set_other hjeq]
      exact hnj j (by omega)

/-- Whether some job has deadline `d`. -/
def occB (x : List ℕ) (n : ℕ) (d : ℕ) : Bool := !(jlist (due x) d n).isEmpty

theorem bucketLoop_spec (Lo : ℕ) (hxg : ∀ i, x.getD i 0 + 2 < B) (hB : 2 < B)
    (hnB : n + 2 < B) (hxB : x.length + 2 < B) (hlen : 2 + n + n ≤ x.length)
    (hjc : jobCount x = n) (hdue : ∀ j, j < n → due x j < Lo) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "n" = n ∧ Lo ≤ (σ.arrs "occ").length ∧
        Lo ≤ (σ.arrs "fj").length ∧ n ≤ (σ.arrs "nj").length ∧
        (∀ d, (σ.arrs "fj").getD d 0 = 0) ∧ (∀ d, (σ.arrs "occ").getD d 0 = 0)) bucketLoop
      (fun _ σ' => σ'.arrs "a" = x ∧ σ'.vars "n" = n ∧
        (∀ d, (σ'.arrs "fj").getD d 0 = hd1 (jlist (due x) d n)) ∧
        (∀ d, (σ'.arrs "occ").getD d 0 = if occB x n d then 1 else 0) ∧
        (∀ j, j < n → (σ'.arrs "nj").getD j 0 = hd1 (jlist (due x) (due x j) j)) ∧
        n ≤ (σ'.arrs "nj").length) (27 * n + 6) := by
  intro σ ⟨ha, hn, hoL, hfL, hnL, hfj0, hocc0⟩
  obtain ⟨σ', hrun, ⟨ha', hn', -, -, -, hnL', hfj', hocc', hnj'⟩, hj'⟩ :=
    (Spec.forRangeZero (B := B) "j" "n" (BkInv x n Lo) n 23 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.2.1)
      (bucketBody_spec Lo hxg hB hnB hxB hlen hjc hdue)) σ
      ⟨by simp [Env.setVar, ha], by simp [Env.setVar, hn], by simp [Env.setVar],
        by simp [Env.setVar, hoL], by simp [Env.setVar, hfL], by simp [Env.setVar, hnL],
        by simpa [Env.setVar, jlist, hd1] using hfj0,
        by simpa [Env.setVar, jlist] using hocc0, by simp [Env.setVar]⟩
  rw [hj'] at hfj' hocc' hnj'
  refine ⟨σ', hrun.mono (by omega), ha', hn', hfj', fun d => ?_, hnj', hnL'⟩
  rw [hocc' d]
  simp only [occB]
  by_cases hl : jlist (due x) d n = [] <;> simp [hl, List.isEmpty_iff]

/-! ### Block Starts, and the Next Deadline Inside a Block -/

open Lax470956Proofs.BlockWalk

/-- Nothing occupied within `e` below `d`. -/
def okAux (occ : ℕ → Bool) (d e : ℕ) : Bool := (List.range e).all fun t => !occ (d - 1 - t)

lemma okAux_succ (occ : ℕ → Bool) (d e : ℕ) :
    okAux occ d (e + 1) = (okAux occ d e && !occ (d - 1 - e)) := by
  simp [okAux, List.range_succ]

lemma nxtAux_le (occ : ℕ → Bool) (d k : ℕ) : nxtAux occ d k ≤ d + k := by
  rcases nxtAux_spec (occ := occ) d k with ⟨h0, -⟩ | ⟨-, -, h2, -⟩
  · rw [h0]; omega
  · exact h2

variable {occ : ℕ → Bool}

/-- The state of the scan around one deadline. -/
def ScInv (occ : ℕ → Bool) (Lo Pm dd : ℕ) (σ : Env) : Prop :=
  σ.vars "dd" = dd ∧ σ.vars "Pm" = Pm ∧ σ.vars "e" ≤ Pm ∧
    (∀ d, (σ.arrs "occ").getD d 0 = if occ d then 1 else 0) ∧
    Lo ≤ (σ.arrs "occ").length ∧
    σ.vars "ok" = (if okAux occ dd (σ.vars "e") then 1 else 0) ∧
    σ.vars "nx" = nxtAux occ (dd + Pm - σ.vars "e") (σ.vars "e")

theorem scanBody_spec (Lo Pm dd : ℕ) (hddB : dd + Pm + 2 < B) (hddL : dd + Pm + 1 ≤ Lo) :
    Spec B (fun σ => ScInv occ Lo Pm dd σ ∧ σ.vars "e" < Pm) scanBody
      (fun σ σ' => ScInv occ Lo Pm dd σ' ∧ σ'.vars "e" = σ.vars "e" + 1) 39 := by
  run_vcg
  all_goals obtain ⟨hdd, hPm, hele, hoc, hoL, hok, hnx⟩ := ‹ScInv occ Lo Pm dd σ›
  all_goals have helt : σ.vars "e" < Pm := ‹σ.vars "e" < Pm›
  all_goals have hlo : (σ.arrs "occ").getD (dd - 1 - σ.vars "e") 0 = if occ (dd - 1 - σ.vars "e") then 1 else 0 := hoc _
  all_goals have hhi : (σ.arrs "occ").getD (dd + Pm - σ.vars "e") 0 = if occ (dd + Pm - σ.vars "e") then 1 else 0 := hoc _
  all_goals have hnxle : σ.vars "nx" ≤ dd + Pm := (by rw [hnx]; have := nxtAux_le occ (dd + Pm - σ.vars "e") (σ.vars "e"); omega)
  all_goals have hokle : σ.vars "ok" ≤ 1 := (by rw [hok]; split <;> omega)
  all_goals try simp only [ScInv, Env.setVar, String.reduceEq, ↓reduceIte, if_pos rfl,
    hdd, hPm, hlo, hhi]
  all_goals try (split <;> omega)
  all_goals try omega
  refine ⟨⟨trivial, trivial, by omega, hoc, hoL, ?_, ?_⟩, trivial⟩
  · rw [okAux_succ]
    cases hc : okAux occ dd (σ.vars "e") <;> cases hc2 : occ (dd - 1 - σ.vars "e") <;>
      simp [hc, hc2, hok]
  · have hq : dd + Pm - (σ.vars "e" + 1) + 1 = dd + Pm - σ.vars "e" := by omega
    rw [nxtAux, hq, hnx]
    cases hc : occ (dd + Pm - σ.vars "e") <;> simp [hc]

/-- The scan, with the deadline read off the state. -/
theorem scanLoop_specG (Lo Pm : ℕ) :
    Spec B (fun σ => σ.vars "Pm" = Pm ∧ σ.vars "ok" = 1 ∧ σ.vars "nx" = 0 ∧
        (∀ d, (σ.arrs "occ").getD d 0 = if occ d then 1 else 0) ∧
        Lo ≤ (σ.arrs "occ").length ∧ σ.vars "dd" + Pm + 2 < B ∧ σ.vars "dd" + Pm + 1 ≤ Lo)
      scanLoop
      (fun σ σ' => σ'.vars "dd" = σ.vars "dd" ∧ σ'.vars "Pm" = Pm ∧
        σ'.vars "ok" = (if okAux occ (σ.vars "dd") Pm then 1 else 0) ∧
        σ'.vars "nx" = nxtAux occ (σ.vars "dd") Pm) (43 * Pm + 6) := by
  intro σ ⟨hPm, hok, hnx, hoc, hoL, hddB, hddL⟩
  obtain ⟨σ', hrun, ⟨hdd', hPm', -, -, -, hok', hnx'⟩, he'⟩ :=
    (Spec.forRangeZero (B := B) "e" "Pm" (ScInv occ Lo Pm (σ.vars "dd")) Pm 39 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.2.1)
      (scanBody_spec (occ := occ) Lo Pm (σ.vars "dd") hddB hddL)) σ
      ⟨by simp [Env.setVar], by simp [Env.setVar, hPm], by simp [Env.setVar],
        by simp only [Env.setVar]; exact hoc, by simp [Env.setVar, hoL],
        by simpa [Env.setVar, okAux] using hok, by simpa [Env.setVar, nxtAux] using hnx⟩
  rw [he'] at hok' hnx'
  refine ⟨σ', hrun.mono (by omega), hdd', hPm', hok', ?_⟩
  rw [hnx', show σ.vars "dd" + Pm - Pm = σ.vars "dd" from by omega]

/-- The state of the block-start pass. -/
def StInv (x : List ℕ) (occ : ℕ → Bool) (n Lo Pm : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "n" = n ∧ σ.vars "Pm" = Pm ∧ σ.vars "j" ≤ n ∧
    (∀ d, (σ.arrs "occ").getD d 0 = if occ d then 1 else 0) ∧
    Lo ≤ (σ.arrs "occ").length ∧ Lo ≤ (σ.arrs "st").length ∧ Lo ≤ (σ.arrs "nx2").length ∧
    (∀ j, j < σ.vars "j" →
      (σ.arrs "st").getD (due x j) 0 = (if okAux occ (due x j) Pm then 1 else 0)) ∧
    (∀ j, j < σ.vars "j" → (σ.arrs "nx2").getD (due x j) 0 = nxtAux occ (due x j) Pm)

theorem startBody_spec (Lo Pm : ℕ) (hxg : ∀ i, x.getD i 0 + 2 < B) (hB : 2 < B)
    (hnB : n + 2 < B) (hxB : x.length + 2 < B) (hlen : 2 + n + n ≤ x.length)
    (hjc : jobCount x = n) (hdueB : ∀ j, j < n → due x j + Pm + 2 < B)
    (hdueL : ∀ j, j < n → due x j + Pm + 1 ≤ Lo) :
    Spec B (fun σ => StInv x occ n Lo Pm σ ∧ σ.vars "j" < n) startBody
      (fun σ σ' => StInv x occ n Lo Pm σ' ∧ σ'.vars "j" = σ.vars "j" + 1) (43 * Pm + 27) := by
  run_vcg [(scanLoop_specG (B := B) (occ := occ) Lo Pm).frame]
  all_goals obtain ⟨ha, hn, hPm, hj, hoc, hoL, hsL, hxL, hst, hnx2⟩ := ‹StInv x occ n Lo Pm σ›
  all_goals have hjlt : σ.vars "j" < n := ‹σ.vars "j" < n›
  all_goals have haL : (σ.arrs "a").length = x.length := (by rw [ha])
  all_goals have hval : (σ.arrs "a").getD (2 + σ.vars "n" + σ.vars "j") 0 = due x (σ.vars "j") := (by rw [ha, hn, due, hjc])
  all_goals have hvB : due x (σ.vars "j") + Pm + 2 < B := hdueB _ hjlt
  all_goals have hvL : due x (σ.vars "j") + Pm + 1 ≤ Lo := hdueL _ hjlt
  all_goals try
    (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Env.setVar, String.reduceEq, ↓reduceIte, hval] <;>
      first
        | exact hPm
        | rfl
        | exact hoc
        | exact hoL
        | exact hvB
        | exact hvL)
  all_goals try
    (obtain ⟨⟨hdd1, hPm1, hok1, hnx1⟩, hfv, hfa, -, -⟩ := ‹(_ ∧ _ ∧ _ ∧ _) ∧ (∀ y ∉ scanLoop.wvars, _) ∧ _›
     have hfn := hfv "n" (by simp [scanLoop, scanBody, Com.wvars])
     have hfj := hfv "j" (by simp [scanLoop, scanBody, Com.wvars])
     have hfa' := hfa "a" (by simp [scanLoop, scanBody, Com.warrs])
     have hfocc := hfa "occ" (by simp [scanLoop, scanBody, Com.warrs])
     have hfst := hfa "st" (by simp [scanLoop, scanBody, Com.warrs])
     have hfnx2 := hfa "nx2" (by simp [scanLoop, scanBody, Com.warrs])
     simp only [Env.setVar, String.reduceEq, ↓reduceIte, hval] at hdd1 hPm1 hok1 hnx1 hfn hfj
     simp only [Env.setVar] at hfa' hfocc hfst hfnx2)
  all_goals try simp only [StInv, Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte,
    if_pos rfl, List.length_set, hval, hdd1, hfn, hfj, hfa', hfocc, hfst, hfnx2, hok1, hnx1]
  all_goals try omega
  all_goals try (split <;> omega)
  all_goals try (have hnl := nxtAux_le occ (due x (σ.vars "j")) Pm; omega)
  refine ⟨⟨ha, hn, ?_, by omega, hoc, hoL, by omega, by omega, ?_, ?_⟩, trivial⟩
  · rw [hfv "Pm" (by simp [scanLoop, scanBody, Com.wvars])]
    simpa [Env.setVar] using hPm
  · intro j hjj
    by_cases hd : due x j = due x (σ.vars "j")
    · rw [hd, getD_set_self (show due x (σ.vars "j") < (σ.arrs "st").length from by omega)]
    · rw [getD_set_other (by exact fun hc => hd hc)]
      have hjne : j ≠ σ.vars "j" := fun hc => hd (by rw [hc])
      exact hst j (by omega)
  · intro j hjj
    by_cases hd : due x j = due x (σ.vars "j")
    · rw [hd, getD_set_self (show due x (σ.vars "j") < (σ.arrs "nx2").length from by omega)]
    · rw [getD_set_other (by exact fun hc => hd hc)]
      have hjne : j ≠ σ.vars "j" := fun hc => hd (by rw [hc])
      exact hnx2 j (by omega)

theorem startLoop_spec (Lo P : ℕ) (hxg : ∀ i, x.getD i 0 + 2 < B) (hB : 2 < B)
    (hnB : n + 2 < B) (hxB : x.length + 2 < B) (hPB : P + 2 < B)
    (hlen : 2 + n + n ≤ x.length) (hjc : jobCount x = n)
    (hdueB : ∀ j, j < n → due x j + P + 2 < B)
    (hdueL : ∀ j, j < n → due x j + P + 1 ≤ Lo)
    (hoccd : ∀ j, j < n → occ (due x j) = true) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "n" = n ∧ σ.vars "P" = P ∧
        (∀ d, (σ.arrs "occ").getD d 0 = if occ d then 1 else 0) ∧
        Lo ≤ (σ.arrs "occ").length ∧ Lo ≤ (σ.arrs "st").length ∧
        Lo ≤ (σ.arrs "nx2").length) startLoop
      (fun _ σ' => σ'.arrs "a" = x ∧ σ'.vars "n" = n ∧
        (∀ j, j < n → (σ'.arrs "st").getD (due x j) 0 =
          (if isStart P occ (due x j) then 1 else 0)) ∧
        (∀ j, j < n → (σ'.arrs "nx2").getD (due x j) 0 = nxt P occ (due x j)))
      ((43 * (P - 1) + 31) * n + 10) := by
  intro σ ⟨ha, hn, hP, hoc, hoL, hsL, hxL⟩
  have heval : (sub (V "P") (lit 1)).evalB B σ = some (P - 1) := by
    have h := SweepBody.evalB_sub (B := B) (σ := σ) (SweepBody.evalB_var (by rw [hP]; omega))
      (SweepBody.evalB_lit (show (1 : ℕ) < B by omega)) (by rw [hP]; omega)
    rwa [hP] at h
  obtain ⟨σ', hrun, ⟨ha', hn', -, -, -, -, -, -, hst', hnx2'⟩, hj'⟩ :=
    (Spec.forRangeZero (B := B) "j" "n" (StInv x occ n Lo (P - 1)) n (43 * (P - 1) + 27)
      (by omega) (fun _ h => h.2.2.2.1) (fun _ h => h.2.1)
      (startBody_spec (occ := occ) Lo (P - 1) hxg hB hnB hxB hlen hjc
        (fun j hj => by have := hdueB j hj; omega)
        (fun j hj => by have := hdueL j hj; omega))) (σ.setVar "Pm" (P - 1))
      ⟨by simp [Env.setVar, ha], by simp [Env.setVar, hn], by simp [Env.setVar],
        by simp [Env.setVar], by simp only [Env.setVar]; exact hoc,
        by simp [Env.setVar, hoL], by simp [Env.setVar, hsL], by simp [Env.setVar, hxL],
        by simp [Env.setVar], by simp [Env.setVar]⟩
  rw [hj'] at hst' hnx2'
  refine ⟨σ', (Run.seq (Run.assign heval) hrun).mono (le_of_eq (by simp only [Expr.size]; ring)),
    ha', hn', fun j hj => ?_, fun j hj => ?_⟩
  · rw [hst' j hj]
    congr 1
    simp only [isStart, okAux, hoccd j hj, Bool.true_and]
  · rw [hnx2' j hj]
    rfl

end Lax470956Proofs.SweepPre
