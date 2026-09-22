import Lax470956Proofs.SweepProg

/-!
The table loops of the sweep.

Each pass over the table is one loop of `S` turns, and each is specified by what it does
to the table as a function.
-/

namespace Lax470956Proofs.SweepTable

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956Proofs.SweepProg

variable {B : ℕ}

/-- The array `nm` holds the table `f`, of size `S`. -/
def Tbl (nm : String) (S : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  (σ.arrs nm).length = S ∧ ∀ c, c < S → (σ.arrs nm).getD c 0 = f c

lemma getD_set_other {A : List ℕ} {i j v : ℕ} (h : j ≠ i) :
    (A.set i v).getD j 0 = A.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]

lemma getD_set_self {A : List ℕ} {i v : ℕ} (h : i < A.length) : (A.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

/-! ### Copying -/

def CInv (src dst : String) (S : ℕ) (f g : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "S" = S ∧ Tbl src S f σ ∧ (σ.arrs dst).length = S ∧ σ.vars "c" ≤ S ∧
    ∀ c, c < S → (σ.arrs dst).getD c 0 = if c < σ.vars "c" then f c else g c

theorem takeBody_spec (S : ℕ) (f g : ℕ → ℕ) (hS : S + 2 < B) (hf : ∀ c, c < S → f c < B) :
    Spec B (fun σ => CInv "V2" "V" S f g σ ∧ σ.vars "c" < S) takeBody
      (fun σ σ' => CInv "V2" "V" S f g σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 20 := by
  run_vcg
  all_goals obtain ⟨hSv, ⟨hlen2, hval2⟩, hlen, hle, hcell⟩ := ‹CInv "V2" "V" S f g σ›
  all_goals have hclt := ‹σ.vars "c" < S›
  all_goals have hv := hval2 _ hclt
  all_goals try omega
  all_goals try (rw [hSv]; omega)
  all_goals try (rw [hlen2]; omega)
  all_goals try (rw [hv]; exact hf _ hclt)
  refine ⟨⟨by simpa [Env.setVar] using hSv, ⟨by simpa [Env.setArr] using hlen2, ?_⟩,
    by simpa [Env.setArr, Env.setVar, List.length_set] using hlen, by simp [Env.setVar]; omega,
    ?_⟩, by simp [Env.setVar]⟩
  · intro c hc
    simp only [Env.setVar, Env.setArr, if_neg (by decide : ¬ ("V2" = "V"))]
    exact hval2 c hc
  · intro c hc
    simp only [Env.setVar, Env.setArr, if_pos rfl, if_true]
    by_cases hce : c = σ.vars "c"
    · subst hce
      rw [getD_set_self (by omega), if_pos (by omega), hv]
    · rw [getD_set_other hce, hcell c hc]
      by_cases h1 : c < σ.vars "c"
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

theorem takeLoop_spec (S : ℕ) (f : ℕ → ℕ) (hS : S + 2 < B) (hf : ∀ c, c < S → f c < B) :
    Spec B (fun σ => σ.vars "S" = S ∧ Tbl "V2" S f σ ∧ (σ.arrs "V").length = S) takeLoop
      (fun _ σ' => Tbl "V" S f σ' ∧ Tbl "V2" S f σ' ∧ σ'.vars "S" = S) (24 * S + 6) := by
  intro σ ⟨hSv, hT2, hlen⟩
  obtain ⟨σ', hrun, hI, hc⟩ :=
    Spec.forRangeZero (B := B) "c" "S"
      (CInv "V2" "V" S f (fun c => (σ.arrs "V").getD c 0)) S 20 (by omega)
      (fun _ h => h.2.2.2.1) (fun _ h => h.1) (takeBody_spec S f _ hS hf) σ
      ⟨by simpa [Env.setVar] using hSv, hT2, by simpa [Env.setVar] using hlen,
        by simp [Env.setVar], fun c hcc => by simp [Env.setVar]⟩
  refine ⟨σ', hrun.mono (by omega), ⟨hI.2.2.1, fun c hcc => ?_⟩, hI.2.1, hI.1⟩
  rw [hI.2.2.2.2 c hcc, if_pos (by omega)]

/-! ### Zeroing -/

def ZInv (nm : String) (S : ℕ) (σ : Env) : Prop :=
  σ.vars "S" = S ∧ (σ.arrs nm).length = S ∧ σ.vars "c" ≤ S ∧
    ∀ c, c < σ.vars "c" → (σ.arrs nm).getD c 0 = 0

theorem zeroBody_spec (nm : String) (S : ℕ) (hS : S + 2 < B) :
    Spec B (fun σ => ZInv nm S σ ∧ σ.vars "c" < S) (zeroBodyOf nm)
      (fun σ σ' => ZInv nm S σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 12 := by
  run_vcg
  all_goals obtain ⟨hSv, hlen, hle, hcell⟩ := ‹ZInv nm S σ›
  all_goals have hclt := ‹σ.vars "c" < S›
  all_goals try omega
  all_goals try (rw [hSv]; omega)
  all_goals try (rw [hlen]; omega)
  refine ⟨⟨by simpa [Env.setVar] using hSv,
    by simpa [Env.setVar, Env.setArr, List.length_set] using hlen,
    by simp [Env.setVar]; omega, fun c hc => ?_⟩, by simp [Env.setVar]⟩
  simp only [Env.setVar, Env.setArr, if_pos rfl, if_true] at hc ⊢
  by_cases hce : c = σ.vars "c"
  · subst hce; exact getD_set_self (by omega)
  · rw [getD_set_other hce]; exact hcell c (by simp at hc; omega)

theorem zeroLoop_spec (nm : String) (S : ℕ) (hS : S + 2 < B) :
    Spec B (fun σ => σ.vars "S" = S ∧ (σ.arrs nm).length = S) (zeroLoopOf nm)
      (fun _ σ' => Tbl nm S (fun _ => 0) σ' ∧ σ'.vars "S" = S) (16 * S + 6) := by
  intro σ ⟨hSv, hlen⟩
  obtain ⟨σ', hrun, hI, hc⟩ :=
    Spec.forRangeZero (B := B) "c" "S" (ZInv nm S) S 12 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.1) (zeroBody_spec nm S hS) σ
      ⟨by simpa [Env.setVar] using hSv, by simpa [Env.setVar] using hlen,
        by simp [Env.setVar], fun c hc => by simp [Env.setVar] at hc⟩
  exact ⟨σ', hrun.mono (by omega), ⟨hI.2.1, fun c hcc => hI.2.2.2 c (by omega)⟩, hI.1⟩

/-! ### The best entry -/

def BInv (S : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "S" = S ∧ Tbl "V" S f σ ∧ σ.vars "c" ≤ S ∧
    (∀ c, c < σ.vars "c" → f c ≤ σ.vars "bst") ∧
    (σ.vars "bst" = 0 ∨ ∃ c, c < σ.vars "c" ∧ f c = σ.vars "bst")

theorem bestBody_spec (S : ℕ) (f : ℕ → ℕ) (hS : S + 2 < B) (hf : ∀ c, c < S → f c < B) :
    Spec B (fun σ => BInv S f σ ∧ σ.vars "c" < S) bestBody
      (fun σ σ' => BInv S f σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 16 := by
  run_vcg
  all_goals obtain ⟨hSv, ⟨hlen, hval⟩, hle, hub, hattn⟩ := ‹BInv S f σ›
  all_goals have hclt := ‹σ.vars "c" < S›
  all_goals have hv := hval _ hclt
  all_goals simp only [BInv, Tbl, Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals have hbstB : σ.vars "bst" < B := (by
    rcases hattn with h | ⟨c, hc, hfc⟩
    · omega
    · have := hf c (by omega); omega)
  all_goals try omega
  all_goals try (rw [hlen]; omega)
  all_goals try (rw [hv]; exact hf _ hclt)
  · refine ⟨⟨hSv, ⟨hlen, hval⟩, by omega, fun c hc => ?_,
      Or.inr ⟨σ.vars "c", by omega, ?_⟩⟩, trivial⟩
    · have hlt := ‹σ.vars "bst" < (σ.arrs "V").getD (σ.vars "c") 0›
      rw [hv] at hlt
      by_cases hce : c = σ.vars "c"
      · subst hce; omega
      · have := hub c (by omega); omega
    · exact hv.symm
  · refine ⟨⟨hSv, ⟨hlen, hval⟩, by omega, fun c hc => ?_, ?_⟩, trivial⟩
    · have hge := ‹¬ σ.vars "bst" < (σ.arrs "V").getD (σ.vars "c") 0›
      rw [hv] at hge
      by_cases hce : c = σ.vars "c"
      · subst hce; omega
      · exact hub c (by omega)
    · rcases hattn with h | ⟨c, hc, hfc⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, by omega, hfc⟩

theorem bestLoop_spec (S : ℕ) (f : ℕ → ℕ) (hS : S + 2 < B) (hf : ∀ c, c < S → f c < B) :
    Spec B (fun σ => σ.vars "S" = S ∧ Tbl "V" S f σ) bestLoop
      (fun _ σ' => Tbl "V" S f σ' ∧ σ'.vars "S" = S ∧ (∀ c, c < S → f c ≤ σ'.vars "bst") ∧
        (σ'.vars "bst" = 0 ∨ ∃ c, c < S ∧ f c = σ'.vars "bst")) (20 * S + 8) := by
  intro σ ⟨hSv, hT⟩
  obtain ⟨σ', hrun, hI, hc⟩ :=
    Spec.forRangeZero (B := B) "c" "S" (BInv S f) S 16 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.1) (bestBody_spec S f hS hf)
      (σ.setVar "bst" 0)
      ⟨by simpa [Env.setVar] using hSv, hT, by simp [Env.setVar],
        fun c hcc => by simp [Env.setVar] at hcc, Or.inl (by simp [Env.setVar])⟩
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono (by simp; omega), hI.2.1,
    hI.1, fun c hcc => hI.2.2.2.1 c (by omega), ?_⟩
  rcases hI.2.2.2.2 with h | ⟨c, hcc, hfc⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, by omega, hfc⟩

theorem clearLoop_spec (S : ℕ) (hS : S + 2 < B) (h1 : 1 ≤ S) (h2 : 1 < B) :
    Spec B (fun σ => σ.vars "S" = S ∧ (σ.arrs "V").length = S) clearLoop
      (fun _ σ' => Tbl "V" S (fun c => if c = 0 then 1 else 0) σ' ∧ σ'.vars "S" = S ∧
        σ'.vars "tp" = 0) (16 * S + 12) := by
  intro σ hσ
  obtain ⟨σ₁, hrun1, ⟨hlen1, hval1⟩, hS1⟩ := zeroLoop_spec (B := B) "V" S hS σ hσ
  refine ⟨((σ₁.setArr "V" 0 1).setVar "tp" 0), ?_, ⟨?_, fun c hc => ?_⟩, ?_, ?_⟩
  · refine (Run.seq hrun1 (Run.seq (Run.store (by simp; omega) (by simp; omega)
      (by rw [hlen1]; omega)) (Run.assign (v := 0) (by simp; omega)))).mono ?_
    simp <;> omega
  · simpa [Env.setVar, Env.setArr, List.length_set] using hlen1
  · simp only [Env.setVar, Env.setArr, if_pos rfl, if_true]
    by_cases hc0 : c = 0
    · subst hc0; rw [getD_set_self (by omega), if_pos rfl]
    · rw [getD_set_other hc0, if_neg hc0, hval1 c hc]
  · simpa [Env.setVar, Env.setArr] using hS1
  · simp [Env.setVar]

lemma dd_le (a b c : ℕ) : a / b / c ≤ a := le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)

lemma ddm_le (a b c : ℕ) : a / b / c * c ≤ a :=
  le_trans (Nat.div_mul_le_self _ _) (Nat.div_le_self _ _)

/-- Capping by truncated subtraction. -/
lemma nat_cap (a b : ℕ) : a - (a - b) = min a b := by omega

/-- The larger of two, by truncated subtraction. -/
lemma nat_mx (a b : ℕ) : a + (b - a) = max a b := by omega

/-! ### Advancing one configuration -/

/-- The array `pw` holds the powers of `P + 1`. -/
def Pw (m P : ℕ) (σ : Env) : Prop :=
  m ≤ (σ.arrs "pw").length ∧ ∀ i, i < m → (σ.arrs "pw").getD i 0 = (P + 1) ^ i

def AInv (m P δ code : ℕ) (σ : Env) : Prop :=
  σ.vars "m" = m ∧ σ.vars "P" = P ∧ σ.vars "del" = δ ∧ σ.vars "c" = code ∧ Pw m P σ ∧
    σ.vars "i" ≤ m ∧
    σ.vars "c2" = Radix.enc P (σ.vars "i") fun i => min (Radix.dig P code i + δ) P

theorem advBody_spec (m P δ code S : ℕ) (hS : (P + 1) ^ m ≤ S) (hcS : code < S)
    (hmB : m + 2 < B) (hB : S + P + δ + 2 < B) :
    Spec B (fun σ => AInv m P δ code σ ∧ σ.vars "i" < m) advBody
      (fun σ σ' => AInv m P δ code σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  have hpow : ∀ k, k ≤ m → (P + 1) ^ k ≤ S := fun k hk =>
    le_trans (Nat.pow_le_pow_right (by omega) hk) hS
  have hencl : ∀ k, k ≤ m →
      Radix.enc P k (fun i => min (Radix.dig P code i + δ) P) < (P + 1) ^ k :=
    fun k hk => Radix.enc_lt fun i _ => by omega
  run_vcg
  all_goals simp only [AInv, Pw, Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals obtain ⟨hm, hP, hdel, hcode, ⟨hpl, hpv⟩, hile, hc2⟩ := ‹σ.vars "m" = m ∧ _›
  all_goals have hilt : σ.vars "i" < m := ‹σ.vars "i" < m›
  all_goals have hpwi := hpv _ hilt
  all_goals have hpwb : (σ.arrs "pw").getD (σ.vars "i") 0 ≤ S := (by
    rw [hpwi]; exact hpow _ hilt.le)
  all_goals have hdig : σ.vars "c" / (σ.arrs "pw").getD (σ.vars "i") 0 -
      σ.vars "c" / (σ.arrs "pw").getD (σ.vars "i") 0 / (σ.vars "P" + 1) * (σ.vars "P" + 1)
      = Radix.dig P code (σ.vars "i") := (by
    rw [hpwi, hP, hcode, Radix.dig]
    have h1 := Nat.mod_add_div (code / (P + 1) ^ (σ.vars "i")) (P + 1)
    have h2 : (P + 1) * (code / (P + 1) ^ (σ.vars "i") / (P + 1))
        = code / (P + 1) ^ (σ.vars "i") / (P + 1) * (P + 1) := Nat.mul_comm _ _
    omega)
  all_goals have hdle : Radix.dig P code (σ.vars "i") ≤ P := Radix.dig_le _ _
  all_goals have hc2b : σ.vars "c2" < (P + 1) ^ (σ.vars "i") := (by
    rw [hc2]; exact hencl _ hile)
  all_goals have hc2S : σ.vars "c2" < S := lt_of_lt_of_le hc2b (hpow _ hile)
  all_goals try simp only [nat_cap]
  all_goals rw [hpwi, hP] at hdig
  all_goals try rw [hpwi]
  all_goals try rw [hP]
  all_goals try rw [hdig]
  all_goals try rw [hdel]
  · refine ⟨⟨hm, rfl, rfl, hcode, ⟨hpl, hpv⟩, by omega, ?_⟩, trivial⟩
    have key : Radix.enc P (σ.vars "i" + 1) (fun k => min (Radix.dig P code k + δ) P)
        = σ.vars "c2" + min (Radix.dig P code (σ.vars "i") + δ) P * (P + 1) ^ (σ.vars "i") := by
      rw [Radix.enc_succ, hc2]
    rw [key]
  all_goals first
    | omega
    | (refine lt_of_le_of_lt (Nat.div_le_self _ _) ?_; omega)
    | (have hnext := lt_of_lt_of_le (hencl (σ.vars "i" + 1) hilt) (hpow (σ.vars "i" + 1) hilt)
       rw [Radix.enc_succ] at hnext
       rw [← hc2] at hnext
       omega)
    | (exact lt_of_le_of_lt (dd_le _ _ _) (by omega))
    | (exact lt_of_le_of_lt (ddm_le _ _ _) (by omega))
    | (rw [hdig] at *; omega)

/-- **Advancing a configuration**: `c2` becomes the number of the configuration `c`
stands for, every machine having been free `del` longer. -/
theorem advLoop_spec (m P δ code S : ℕ) (hS : (P + 1) ^ m ≤ S) (hcS : code < S)
    (hmB : m + 2 < B) (hB : S + P + δ + 2 < B) :
    Spec B (fun σ => σ.vars "m" = m ∧ σ.vars "P" = P ∧ σ.vars "del" = δ ∧ σ.vars "c" = code ∧
        Pw m P σ) advLoop
      (fun _ σ' => σ'.vars "c2" = Radix.enc P m (fun i => min (Radix.dig P code i + δ) P) ∧
        σ'.vars "m" = m ∧ σ'.vars "P" = P ∧ σ'.vars "del" = δ ∧ σ'.vars "c" = code ∧
        Pw m P σ') (44 * m + 8) := by
  intro σ ⟨hm, hP, hdel, hcode, hpw⟩
  obtain ⟨σ', hrun, hI, hi⟩ :=
    Spec.forRangeZero (B := B) "i" "m" (AInv m P δ code) m 40 (by omega)
      (fun _ h => h.2.2.2.2.2.1) (fun _ h => h.1)
      (advBody_spec m P δ code S hS hcS hmB hB) (σ.setVar "c2" 0)
      ⟨by simpa [Env.setVar] using hm, by simpa [Env.setVar] using hP,
        by simpa [Env.setVar] using hdel, by simpa [Env.setVar] using hcode,
        hpw, by simp [Env.setVar], by simp [Env.setVar, Radix.enc]⟩
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono (by simp <;> omega), ?_,
    hI.1, hI.2.1, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2.1⟩
  rw [hI.2.2.2.2.2.2, hi]

/-! ### The shift -/

/-- The configuration `c` stands for, once every machine has been free `del` longer. -/
def advOf (P m δ c : ℕ) : ℕ := Radix.enc P m fun i => min (Radix.dig P c i + δ) P

lemma advOf_lt {P m δ c S : ℕ} (hS : (P + 1) ^ m ≤ S) : advOf P m δ c < S :=
  lt_of_lt_of_le (Radix.enc_lt fun i _ => Nat.min_le_right _ _) hS

/-- What the shift leaves in `Vt`: the best value pushed into each configuration by the
configurations below `b`. -/
def pushed (P m δ : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | b + 1, c' =>
      if advOf P m δ b = c' then max (pushed P m δ f b c') (f b) else pushed P m δ f b c'

@[simp] def pushed_zero (P m δ : ℕ) (f : ℕ → ℕ) (c' : ℕ) : pushed P m δ f 0 c' = 0 := rfl

lemma pushed_succ (P m δ : ℕ) (f : ℕ → ℕ) (b c' : ℕ) :
    pushed P m δ f (b + 1) c' =
      if advOf P m δ b = c' then max (pushed P m δ f b c') (f b)
      else pushed P m δ f b c' := rfl

lemma pushed_le (P m δ : ℕ) (f : ℕ → ℕ) (b c' K : ℕ) (hf : ∀ c, c < b → f c ≤ K) :
    pushed P m δ f b c' ≤ K := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [pushed_succ]
      split
      · exact max_le (ih fun c hc => hf c (by omega)) (hf b (by omega))
      · exact ih fun c hc => hf c (by omega)

/-- The advance, with the configuration read off the state. -/
theorem advLoop_spec' (m P δ S : ℕ) (hS : (P + 1) ^ m ≤ S) (hmB : m + 2 < B)
    (hB : S + P + δ + 2 < B) :
    Spec B (fun σ => σ.vars "m" = m ∧ σ.vars "P" = P ∧ σ.vars "del" = δ ∧ σ.vars "c" < S ∧
        Pw m P σ) advLoop
      (fun σ σ' => σ'.vars "c2" = advOf P m δ (σ.vars "c") ∧ σ'.vars "c" = σ.vars "c")
      (44 * m + 8) := by
  intro σ ⟨hm, hP, hdel, hcS, hpw⟩
  obtain ⟨σ', hrun, h1, -, -, -, h5, -⟩ :=
    advLoop_spec (B := B) m P δ (σ.vars "c") S hS hcS hmB hB σ ⟨hm, hP, hdel, rfl, hpw⟩
  exact ⟨σ', hrun, h1, h5⟩

lemma wvars_advLoop : advLoop.wvars = ["c2", "i", "u", "u", "c2", "i"] := by
  simp [advLoop, advBody, Com.wvars]

lemma warrs_advLoop : advLoop.warrs = [] := by simp [advLoop, advBody, Com.warrs]

/-- The state during the shift. -/
def SInv (m P δ S : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "S" = S ∧ σ.vars "m" = m ∧ σ.vars "P" = P ∧ σ.vars "del" = δ ∧ Pw m P σ ∧
    Tbl "V" S f σ ∧ (σ.arrs "Vt").length = S ∧ σ.vars "c" ≤ S ∧
    ∀ c', c' < S → (σ.arrs "Vt").getD c' 0 = pushed P m δ f (σ.vars "c") c'

theorem shiftBody_spec (m P δ S K : ℕ) (f : ℕ → ℕ) (hS : (P + 1) ^ m ≤ S)
    (hmB : m + 2 < B) (hB : S + P + δ + 2 < B) (hfK : ∀ c, f c ≤ K) (hKB : K < B) :
    Spec B (fun σ => SInv m P δ S f σ ∧ σ.vars "c" < S) shiftBody
      (fun σ σ' => SInv m P δ S f σ' ∧ σ'.vars "c" = σ.vars "c" + 1) (44 * m + 40) := by
  run_vcg [(advLoop_spec' (B := B) m P δ S hS hmB hB).frame]
  all_goals obtain ⟨hSv, hm, hP, hdel, hpw, ⟨hlenV, hvalV⟩, hlenVt, hcle, hVt⟩ :=
    ‹SInv m P δ S f σ›
  all_goals have hclt : σ.vars "c" < S := ‹σ.vars "c" < S›
  all_goals have hvc := hvalV _ hclt
  all_goals have hfKc := hfK (σ.vars "c")
  all_goals have hadvS : advOf P m δ (σ.vars "c") < S := advOf_lt hS
  all_goals have hpushK : ∀ b c', pushed P m δ f b c' ≤ K :=
    fun b c' => pushed_le P m δ f b c' K fun c _ => hfK c
  all_goals try
    (obtain ⟨⟨hc2, hcsame⟩, hfv, hfa, -, -⟩ := ‹(_ ∧ _) ∧ (∀ y ∉ advLoop.wvars, _) ∧ _›
     have hSw := hfv "S" (by simp [wvars_advLoop])
     have hcw := hfv "c" (by simp [wvars_advLoop])
     have hmw := hfv "m" (by simp [wvars_advLoop])
     have hPw' := hfv "P" (by simp [wvars_advLoop])
     have hdw := hfv "del" (by simp [wvars_advLoop])
     have hVw := hfa "V" (by simp [warrs_advLoop])
     have hVtw := hfa "Vt" (by simp [warrs_advLoop])
     have hpww := hfa "pw" (by simp [warrs_advLoop]))
  all_goals try simp only [SInv, Tbl, Pw, Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte,
    if_pos rfl, if_true, List.length_set, hc2, hcw, hVtw, hVw, hSw, hmw, hPw', hdw, hpww]
  · refine ⟨⟨hSv, hm, hP, hdel, hpw, ⟨hlenV, hvalV⟩, hlenVt, by omega, fun c' hc' => ?_⟩,
      trivial⟩
    rw [pushed_succ, hvc]
    by_cases hce : c' = advOf P m δ (σ.vars "c")
    · subst hce
      rw [getD_set_self (by omega), if_pos rfl, hVt _ hc']
      omega
    · rw [getD_set_other hce, hVt c' hc', if_neg (by intro h; exact hce h.symm)]
  all_goals first
    | omega
    | exact ⟨hm, hP, hdel, hclt, hpw⟩
    | (rw [hvc]; omega)
    | (rw [hlenV]; omega)
    | (rw [hVt _ hadvS]; exact lt_of_le_of_lt (hpushK _ _) hKB)
    | (rw [hVt _ hadvS, hvc]
       have := hpushK (σ.vars "c") (advOf P m δ (σ.vars "c"))
       omega)

/-- **The shift**: `Vt` receives, for every configuration, the best value of a
configuration that advances to it. -/
theorem shiftLoop_spec (m P δ S K : ℕ) (f : ℕ → ℕ) (hS : (P + 1) ^ m ≤ S)
    (hmB : m + 2 < B) (hB : S + P + δ + 2 < B) (hfK : ∀ c, f c ≤ K) (hKB : K < B) :
    Spec B (fun σ => σ.vars "S" = S ∧ σ.vars "m" = m ∧ σ.vars "P" = P ∧ σ.vars "del" = δ ∧
        Pw m P σ ∧ Tbl "V" S f σ ∧ (σ.arrs "Vt").length = S) shiftLoop
      (fun _ σ' => SInv m P δ S f σ' ∧ Tbl "Vt" S (pushed P m δ f S) σ')
      ((16 * S + 6) + (44 * m + 44) * S + 6) := by
  intro σ ⟨hSv, hm, hP, hdel, hpw, hT, hlenVt⟩
  obtain ⟨σ₁, hrun1, ⟨⟨hlen1, hval1⟩, hS1⟩, hfv, hfa, -, -⟩ :=
    (zeroLoop_spec (B := B) "Vt" S (by omega)).frame σ ⟨hSv, hlenVt⟩
  have hzw : ∀ y, y ≠ "c" → σ₁.vars y = σ.vars y := fun y hy =>
    hfv y (by simp [zeroLoopOf, zeroBodyOf, Com.wvars, hy])
  have hza : ∀ a, a ≠ "Vt" → σ₁.arrs a = σ.arrs a := fun a ha =>
    hfa a (by simp [zeroLoopOf, zeroBodyOf, Com.warrs, ha])
  obtain ⟨σ₂, hrun2, hI, hc⟩ :=
    Spec.forRangeZero (B := B) "c" "S" (SInv m P δ S f) S (44 * m + 40) (by omega)
      (fun _ h => h.2.2.2.2.2.2.2.1) (fun _ h => h.1)
      (shiftBody_spec m P δ S K f hS hmB hB hfK hKB) σ₁
      ⟨by simpa [Env.setVar] using hS1, by simp [Env.setVar, hzw "m" (by decide)]; exact hm,
        by simp [Env.setVar, hzw "P" (by decide)]; exact hP,
        by simp [Env.setVar, hzw "del" (by decide)]; exact hdel,
        by simpa [Env.setVar, Pw, hza "pw" (by decide)] using hpw,
        by simpa [Env.setVar, Tbl, hza "V" (by decide)] using hT, hlen1,
        by simp [Env.setVar], fun c' hc' => by simp [Env.setVar]; exact hval1 c' hc'⟩
  refine ⟨σ₂, (Run.seq hrun1 hrun2).mono (le_of_eq (by ring)), hI, hI.2.2.2.2.2.2.1,
    fun c' hc' => ?_⟩
  rw [hI.2.2.2.2.2.2.2.2 c' hc', hc]

lemma wvars_shiftLoop : ∀ x ∈ shiftLoop.wvars, x ∈ ["c", "c2", "i", "u"] := by
  intro x hx
  simp only [shiftLoop, zeroLoop, zeroLoopOf, zeroBodyOf, shiftBody, advLoop, advBody,
    Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  tauto

lemma warrs_shiftLoop : ∀ x ∈ shiftLoop.warrs, x ∈ ["Vt"] := by
  intro x hx
  simp only [shiftLoop, zeroLoop, zeroLoopOf, zeroBodyOf, shiftBody, advLoop, advBody,
    Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  tauto

/-! ### Installing the shifted table -/

def MInv (S : ℕ) (g : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "S" = S ∧ Tbl "Vt" S g σ ∧ (σ.arrs "V").length = S ∧ (σ.arrs "V2").length = S ∧
    σ.vars "c" ≤ S ∧ (∀ c, c < σ.vars "c" → (σ.arrs "V").getD c 0 = g c) ∧
    (∀ c, c < σ.vars "c" → (σ.arrs "V2").getD c 0 = g c)

theorem commitBody_spec (S K : ℕ) (g : ℕ → ℕ) (hS : S + 2 < B) (hg : ∀ c, g c ≤ K)
    (hKB : K < B) :
    Spec B (fun σ => MInv S g σ ∧ σ.vars "c" < S) commitBody
      (fun σ σ' => MInv S g σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 24 := by
  run_vcg
  all_goals obtain ⟨hSv, ⟨hlenT, hvalT⟩, hlenV, hlenV2, hcle, hV, hV2⟩ := ‹MInv S g σ›
  all_goals have hclt : σ.vars "c" < S := ‹σ.vars "c" < S›
  all_goals have hvt := hvalT _ hclt
  all_goals have hgK := hg (σ.vars "c")
  all_goals try simp only [MInv, Tbl, Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte,
    if_pos rfl, if_true, List.length_set]
  · refine ⟨⟨hSv, ⟨hlenT, hvalT⟩, hlenV, hlenV2, by omega, fun c hc => ?_, fun c hc => ?_⟩,
      trivial⟩
    · by_cases hce : c = σ.vars "c"
      · subst hce; rw [getD_set_self (by omega), hvt]
      · rw [getD_set_other hce]; exact hV c (by omega)
    · by_cases hce : c = σ.vars "c"
      · subst hce; rw [getD_set_self (by omega), hvt]
      · rw [getD_set_other hce]; exact hV2 c (by omega)
  all_goals first
    | omega
    | (rw [hlenT]; omega)
    | (rw [hvt]; omega)
    | (rw [hlenV]; omega)
    | (rw [hlenV2]; omega)

/-- **Time advances**: both tables become the shifted table. -/
theorem commitLoop_spec (m P δ S K : ℕ) (f : ℕ → ℕ) (hS : (P + 1) ^ m ≤ S)
    (hmB : m + 2 < B) (hB : S + P + δ + 2 < B) (hfK : ∀ c, f c ≤ K) (hKB : K < B) :
    Spec B (fun σ => σ.vars "S" = S ∧ σ.vars "m" = m ∧ σ.vars "P" = P ∧ σ.vars "del" = δ ∧
        Pw m P σ ∧ Tbl "V" S f σ ∧ (σ.arrs "Vt").length = S ∧ (σ.arrs "V2").length = S)
      commitLoop
      (fun _ σ' => Tbl "V" S (pushed P m δ f S) σ' ∧ Tbl "V2" S (pushed P m δ f S) σ' ∧
        σ'.vars "S" = S) ((44 * m + 88) * S + 18) := by
  intro σ ⟨hSv, hm, hP, hdel, hpw, hT, hlenVt, hlenV2⟩
  obtain ⟨σ₁, hrun1, ⟨hI1, hT1⟩, hfv, hfa, -, -⟩ :=
    (shiftLoop_spec (B := B) m P δ S K f hS hmB hB hfK hKB).frame σ
      ⟨hSv, hm, hP, hdel, hpw, hT, hlenVt⟩
  have hsw : ∀ y, y ≠ "c" → y ≠ "c2" → y ≠ "i" → y ≠ "u" → σ₁.vars y = σ.vars y := by
    intro y h1 h2 h3 h4
    refine hfv y fun hmem => ?_
    have := wvars_shiftLoop y hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h <;> exact absurd h (by assumption)
  have hsa : ∀ a, a ≠ "Vt" → σ₁.arrs a = σ.arrs a := by
    intro a ha
    refine hfa a fun hmem => ?_
    have := warrs_shiftLoop a hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    exact absurd this ha
  obtain ⟨σ₂, hrun2, hI2, hc2⟩ :=
    Spec.forRangeZero (B := B) "c" "S" (MInv S (pushed P m δ f S)) S 24 (by omega)
      (fun _ h => h.2.2.2.2.1) (fun _ h => h.1)
      (commitBody_spec S K (pushed P m δ f S) (by omega)
        (fun c => pushed_le P m δ f S c K fun c' _ => hfK c') hKB) σ₁
      ⟨by simpa [Env.setVar] using hI1.1, by simpa [Env.setVar, Tbl] using hT1,
        by simpa [Env.setVar, Tbl] using hI1.2.2.2.2.2.1.1,
        by simp [Env.setVar, hsa "V2" (by decide), hlenV2],
        by simp [Env.setVar], fun c hc => by simp [Env.setVar] at hc,
        fun c hc => by simp [Env.setVar] at hc⟩
  obtain ⟨hs2, -, hlv, hlv2, -, hcv, hcv2⟩ := hI2
  exact ⟨σ₂, (Run.seq hrun1 hrun2).mono (le_of_eq (by ring)),
    ⟨hlv, fun c hc => hcv c (by omega)⟩, ⟨hlv2, fun c hc => hcv2 c (by omega)⟩, hs2⟩

lemma pushed_ge {P m δ : ℕ} {f : ℕ → ℕ} {b c c' : ℕ} (hc : c < b)
    (he : advOf P m δ c = c') : f c ≤ pushed P m δ f b c' := by
  induction b with
  | zero => omega
  | succ b ih =>
      rw [pushed_succ]
      rcases Nat.lt_or_ge c b with h | h
      · split
        · exact le_trans (ih h) (le_max_left _ _)
        · exact ih h
      · have hcb : c = b := by omega
        subst hcb
        rw [if_pos he]
        exact le_max_right _ _

lemma pushed_cases (P m δ : ℕ) (f : ℕ → ℕ) (b c' : ℕ) :
    pushed P m δ f b c' = 0 ∨
      ∃ c, c < b ∧ advOf P m δ c = c' ∧ pushed P m δ f b c' = f c := by
  induction b with
  | zero => exact Or.inl rfl
  | succ b ih =>
      rw [pushed_succ]
      by_cases h : advOf P m δ b = c'
      · rw [if_pos h]
        rcases Nat.le_total (pushed P m δ f b c') (f b) with hle | hle
        · exact Or.inr ⟨b, by omega, h, by omega⟩
        · rcases ih with h0 | ⟨c, hc, he, heq⟩
          · exact Or.inr ⟨b, by omega, h, by omega⟩
          · exact Or.inr ⟨c, by omega, he, by omega⟩
      · rw [if_neg h]
        rcases ih with h0 | ⟨c, hc, he, heq⟩
        · exact Or.inl h0
        · exact Or.inr ⟨c, by omega, he, heq⟩

/-! ### Placing a job -/

/-- The configuration `c` with machine `i` freshly occupied. -/
def zeroAt (P i c : ℕ) : ℕ := c - Radix.dig P c i * (P + 1) ^ i

/-- What the relaxation leaves in `V2`, from the configurations below `b`. -/
def relaxed (P mi pj wj C : ℕ) (f g : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, c' => g c'
  | b + 1, c' =>
      if f b ≠ 0 ∧ pj ≤ Radix.dig P b mi ∧ zeroAt P mi b = c'
      then max (relaxed P mi pj wj C f g b c') (min (f b + wj) C)
      else relaxed P mi pj wj C f g b c'

lemma relaxed_succ (P mi pj wj C : ℕ) (f g : ℕ → ℕ) (b c' : ℕ) :
    relaxed P mi pj wj C f g (b + 1) c' =
      if f b ≠ 0 ∧ pj ≤ Radix.dig P b mi ∧ zeroAt P mi b = c'
      then max (relaxed P mi pj wj C f g b c') (min (f b + wj) C)
      else relaxed P mi pj wj C f g b c' := rfl

lemma relaxed_congr_g {P mi pj wj C : ℕ} {f g g' : ℕ → ℕ} {b c' : ℕ} (h : g c' = g' c') :
    relaxed P mi pj wj C f g b c' = relaxed P mi pj wj C f g' b c' := by
  induction b with
  | zero => exact h
  | succ b ih => rw [relaxed_succ, relaxed_succ, ih]

lemma relaxed_le (P mi pj wj C : ℕ) (f g : ℕ → ℕ) (b c' K : ℕ) (hg : ∀ c, g c ≤ K)
    (hC : C ≤ K) : relaxed P mi pj wj C f g b c' ≤ K := by
  induction b with
  | zero => exact hg c'
  | succ b ih =>
      rw [relaxed_succ]
      split
      · exact max_le ih (le_trans (Nat.min_le_right _ _) hC)
      · exact ih

lemma zeroAt_le (P i c : ℕ) : zeroAt P i c ≤ c := Nat.sub_le _ _

lemma dig_mul_le (P c i : ℕ) : Radix.dig P c i * (P + 1) ^ i ≤ c :=
  le_trans (Nat.mul_le_mul_right _ (Nat.mod_le _ _)) (Nat.div_mul_le_self _ _)

lemma relaxed_ge_base {P mi pj wj C : ℕ} {f g : ℕ → ℕ} (b c' : ℕ) :
    g c' ≤ relaxed P mi pj wj C f g b c' := by
  induction b with
  | zero => exact le_refl _
  | succ b ih =>
      rw [relaxed_succ]
      split
      · exact le_trans ih (le_max_left _ _)
      · exact ih

lemma relaxed_ge {P mi pj wj C : ℕ} {f g : ℕ → ℕ} {b c c' : ℕ} (hc : c < b)
    (hf : f c ≠ 0) (hp : pj ≤ Radix.dig P c mi) (hz : zeroAt P mi c = c') :
    min (f c + wj) C ≤ relaxed P mi pj wj C f g b c' := by
  induction b with
  | zero => omega
  | succ b ih =>
      rw [relaxed_succ]
      rcases Nat.lt_or_ge c b with h | h
      · split
        · exact le_trans (ih h) (le_max_left _ _)
        · exact ih h
      · have hcb : c = b := by omega
        subst hcb
        rw [if_pos ⟨hf, hp, hz⟩]
        exact le_max_right _ _

lemma relaxed_cases (P mi pj wj C : ℕ) (f g : ℕ → ℕ) (b c' : ℕ) :
    relaxed P mi pj wj C f g b c' = g c' ∨
      ∃ c, c < b ∧ f c ≠ 0 ∧ pj ≤ Radix.dig P c mi ∧ zeroAt P mi c = c' ∧
        relaxed P mi pj wj C f g b c' = min (f c + wj) C := by
  induction b with
  | zero => exact Or.inl rfl
  | succ b ih =>
      rw [relaxed_succ]
      by_cases h : f b ≠ 0 ∧ pj ≤ Radix.dig P b mi ∧ zeroAt P mi b = c'
      · rw [if_pos h]
        rcases Nat.le_total (relaxed P mi pj wj C f g b c') (min (f b + wj) C) with hle | hle
        · exact Or.inr ⟨b, by omega, h.1, h.2.1, h.2.2, by omega⟩
        · rcases ih with h0 | ⟨c, hc, h1, h2, h3, heq⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨c, by omega, h1, h2, h3, by omega⟩
      · rw [if_neg h]
        rcases ih with h0 | ⟨c, hc, h1, h2, h3, heq⟩
        · exact Or.inl h0
        · exact Or.inr ⟨c, by omega, h1, h2, h3, heq⟩

def RInv (m P S mi pj wj C : ℕ) (f g : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "S" = S ∧ σ.vars "P" = P ∧ σ.vars "mi" = mi ∧ σ.vars "pj" = pj ∧
    σ.vars "wj" = wj ∧ σ.vars "cap" + 1 = C ∧ mi < m ∧ Pw m P σ ∧ Tbl "V" S f σ ∧
    σ.vars "c" ≤ S ∧ Tbl "V2" S (relaxed P mi pj wj C f g (σ.vars "c")) σ

theorem relaxBody_spec (m P S mi pj wj C K : ℕ) (f g : ℕ → ℕ) (hSB : S + 2 < B)
    (hS : (P + 1) ^ m ≤ S) (hmB : m + 2 < B) (hPB : P + 2 < B) (hpjB : pj < B)
    (hfK : ∀ c, f c ≤ K) (hgK : ∀ c, g c ≤ K) (hCK : C ≤ K) (hKB : K + wj + 2 < B) :
    Spec B (fun σ => RInv m P S mi pj wj C f g σ ∧ σ.vars "c" < S) relaxBody
      (fun σ σ' => RInv m P S mi pj wj C f g σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 80 := by
  run_vcg
  all_goals obtain ⟨hSv, hP, hmi, hpj, hwj, hcap, hmim, ⟨hpl, hpv⟩, ⟨hlenV, hvalV⟩, hcle,
    ⟨hlen2, hval2⟩⟩ := ‹RInv m P S mi pj wj C f g σ›
  all_goals have hclt : σ.vars "c" < S := ‹σ.vars "c" < S›
  all_goals have hvc := hvalV _ hclt
  all_goals have hfKc := hfK (σ.vars "c")
  all_goals have hpwi := hpv _ hmim
  all_goals have hdig : σ.vars "c" / (σ.arrs "pw").getD (σ.vars "mi") 0 -
      σ.vars "c" / (σ.arrs "pw").getD (σ.vars "mi") 0 / (σ.vars "P" + 1) * (σ.vars "P" + 1)
      = Radix.dig P (σ.vars "c") mi := (by
    rw [hmi, hpwi, hP, Radix.dig]
    have h1 := Nat.mod_add_div (σ.vars "c" / (P + 1) ^ mi) (P + 1)
    have h2 : (P + 1) * (σ.vars "c" / (P + 1) ^ mi / (P + 1))
        = σ.vars "c" / (P + 1) ^ mi / (P + 1) * (P + 1) := Nat.mul_comm _ _
    omega)
  all_goals have hzero : σ.vars "c" - Radix.dig P (σ.vars "c") mi *
      (σ.arrs "pw").getD (σ.vars "mi") 0 = zeroAt P mi (σ.vars "c") := (by
    rw [hmi, hpwi, zeroAt])
  all_goals have hzS : zeroAt P mi (σ.vars "c") < S :=
    lt_of_le_of_lt (zeroAt_le _ _ _) hclt
  all_goals have hrelK : ∀ b c', relaxed P mi pj wj C f g b c' ≤ K :=
    fun b c' => relaxed_le P mi pj wj C f g b c' K hgK hCK
  all_goals have hpwb : (σ.arrs "pw").getD (σ.vars "mi") 0 ≤ S := (by
    rw [hmi, hpwi]; exact le_trans (Nat.pow_le_pow_right (by omega) hmim.le) hS)
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try simp only [RInv, Tbl, Pw, Env.setVar, Env.setArr, String.reduceEq,
    ↓reduceIte, if_pos rfl, if_true, List.length_set, hdig, hzero, nat_cap, nat_mx]
  · refine ⟨⟨hSv, hP, hmi, hpj, hwj, hcap, hmim, ⟨hpl, hpv⟩, ⟨hlenV, hvalV⟩, by omega,
      hlen2, fun c' hc' => ?_⟩, trivial⟩
    have hlt : Radix.dig P (σ.vars "c") mi < pj := by
      have h := ‹(_ : ℕ) < σ.vars "pj"›
      rw [hdig, hpj] at h
      exact h
    rw [hval2 c' hc', relaxed_succ, if_neg (by rintro ⟨-, h, -⟩; omega)]
  · refine ⟨⟨hSv, hP, hmi, hpj, hwj, hcap, hmim, ⟨hpl, hpv⟩, ⟨hlenV, hvalV⟩, by omega,
      hlen2, fun c' hc' => ?_⟩, trivial⟩
    have hge : pj ≤ Radix.dig P (σ.vars "c") mi := by
      have h := ‹¬ (_ : ℕ) < σ.vars "pj"›
      rw [hdig, hpj] at h
      omega
    have hpos : f (σ.vars "c") ≠ 0 := by
      have h := ‹0 < (σ.arrs "V").getD (σ.vars "c") 0›
      rw [hvc] at h
      omega
    by_cases hce : c' = zeroAt P mi (σ.vars "c")
    · subst hce
      rw [getD_set_self (by omega), relaxed_succ, if_pos ⟨hpos, hge, rfl⟩, hval2 _ hc',
        hvc, hwj, hcap]
    · rw [getD_set_other hce, hval2 c' hc', relaxed_succ,
        if_neg (by rintro ⟨-, -, h⟩; exact hce h.symm)]
  · refine ⟨⟨hSv, hP, hmi, hpj, hwj, hcap, hmim, ⟨hpl, hpv⟩, ⟨hlenV, hvalV⟩, by omega,
      hlen2, fun c' hc' => ?_⟩, trivial⟩
    have hz : f (σ.vars "c") = 0 := by
      have h := ‹¬ 0 < (σ.arrs "V").getD (σ.vars "c") 0›
      rw [hvc] at h
      omega
    rw [hval2 c' hc', relaxed_succ, if_neg (by rintro ⟨h, -, -⟩; exact h hz)]
  all_goals first
    | omega
    | (rw [hlenV]; omega)
    | (rw [hvc]; omega)
    | (rw [hmi]; omega)
    | (rw [hmi]; rw [hpl.le] at *; omega)
    | (rw [hpwi]; omega)
    | (exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
    | (rw [hlen2]; omega)
    | (rw [hval2 _ hzS]; exact lt_of_le_of_lt (hrelK _ _) (by omega))
    | (rw [hP]; omega)
    | (rw [hwj]; omega)
    | (rw [hcap]; omega)
    | (exact lt_of_le_of_lt (dd_le _ _ _) (by omega))
    | (exact lt_of_le_of_lt (ddm_le _ _ _) (by omega))
    | (exact lt_of_le_of_lt (Radix.dig_le _ _) (by omega))
    | (rw [hpj]; omega)
    | (exact lt_of_le_of_lt (le_trans (Nat.sub_le _ _) hclt.le) (by omega))
    | (exact lt_of_le_of_lt (zeroAt_le _ _ _) (by omega))
    | (rw [hmi, hpwi]; exact lt_of_le_of_lt (dig_mul_le _ _ _) (by omega))
    | (rw [hval2 _ hzS, hvc, hwj, hcap]
       exact max_lt (lt_of_le_of_lt (hrelK _ _) (by omega))
         (lt_of_le_of_lt (Nat.min_le_left _ _) (by omega)))

/-- **Placing a job**: `V2` receives the value of every configuration that can take the
job on machine `mi`, capped. -/
theorem relaxLoop_spec (m P S mi pj wj C K : ℕ) (f g : ℕ → ℕ) (hSB : S + 2 < B)
    (hS : (P + 1) ^ m ≤ S) (hmB : m + 2 < B) (hPB : P + 2 < B) (hpjB : pj < B)
    (hfK : ∀ c, f c ≤ K) (hgK : ∀ c, g c ≤ K) (hCK : C ≤ K) (hKB : K + wj + 2 < B) :
    Spec B (fun σ => σ.vars "S" = S ∧ σ.vars "P" = P ∧ σ.vars "mi" = mi ∧
        σ.vars "pj" = pj ∧ σ.vars "wj" = wj ∧ σ.vars "cap" + 1 = C ∧ mi < m ∧ Pw m P σ ∧
        Tbl "V" S f σ ∧ Tbl "V2" S g σ) relaxLoop
      (fun _ σ' => Tbl "V2" S (relaxed P mi pj wj C f g S) σ' ∧ Tbl "V" S f σ' ∧
        σ'.vars "S" = S) (84 * S + 6) := by
  intro σ ⟨hSv, hP, hmi, hpj, hwj, hcap, hmim, hpw, hT, hT2⟩
  obtain ⟨σ', hrun, hI, hc⟩ :=
    Spec.forRangeZero (B := B) "c" "S" (RInv m P S mi pj wj C f g) S 80 (by omega)
      (fun _ h => h.2.2.2.2.2.2.2.2.2.1) (fun _ h => h.1)
      (relaxBody_spec m P S mi pj wj C K f g hSB hS hmB hPB hpjB hfK hgK hCK hKB) σ
      ⟨by simpa [Env.setVar] using hSv, by simpa [Env.setVar] using hP,
        by simpa [Env.setVar] using hmi, by simpa [Env.setVar] using hpj,
        by simpa [Env.setVar] using hwj, by simpa [Env.setVar] using hcap, hmim, hpw, hT,
        by simp [Env.setVar], by simpa [Env.setVar, Tbl, relaxed] using hT2⟩
  obtain ⟨hs, -, -, -, -, -, -, -, hTV, -, hTV2⟩ := hI
  rw [hc] at hTV2
  exact ⟨σ', hrun.mono (by omega), hTV2, hTV, hs⟩

/-- The relaxation, with everything read off the state. -/
theorem relaxLoop_specG (m P S C K : ℕ) (f : ℕ → ℕ) (hSB : S + 2 < B)
    (hS : (P + 1) ^ m ≤ S) (hmB : m + 2 < B) (hPB : P + 2 < B)
    (hfK : ∀ c, f c ≤ K) (hCK : C ≤ K) :
    Spec B (fun σ => σ.vars "S" = S ∧ σ.vars "P" = P ∧ σ.vars "mi" < m ∧
        σ.vars "cap" + 1 = C ∧ Pw m P σ ∧ Tbl "V" S f σ ∧ (σ.arrs "V2").length = S ∧
        (∀ c, (σ.arrs "V2").getD c 0 ≤ K) ∧
        σ.vars "pj" < B ∧ K + σ.vars "wj" + 2 < B) relaxLoop
      (fun σ σ' => Tbl "V2" S
          (relaxed P (σ.vars "mi") (σ.vars "pj") (σ.vars "wj") C f
            (fun c => (σ.arrs "V2").getD c 0) S) σ' ∧
        Tbl "V" S f σ' ∧ σ'.vars "S" = S) (84 * S + 6) := by
  intro σ ⟨hSv, hP, hmi, hcap, hpw, hT, hlen2, hg, hpjB, hKB⟩
  exact relaxLoop_spec (B := B) m P S (σ.vars "mi") (σ.vars "pj") (σ.vars "wj") C K f
    (fun c => (σ.arrs "V2").getD c 0) hSB hS hmB hPB hpjB hfK hg hCK hKB σ
    ⟨hSv, hP, rfl, rfl, rfl, hcap, hmi, hpw, hT, ⟨hlen2, fun c _ => rfl⟩⟩

/-- **Closing a block**: the running total takes in the block's best, capped. -/
theorem closeBlock_spec (S C : ℕ) (f : ℕ → ℕ) (hS : S + 2 < B)
    (hf : ∀ c, c < S → f c ≤ C + 1) (hCB : 2 * C + 4 < B) :
    Spec B (fun σ => σ.vars "S" = S ∧ Tbl "V" S f σ ∧ σ.vars "cap" = C ∧ σ.vars "acc" ≤ C)
      closeBlock
      (fun σ σ' => (∃ bst, (∀ c, c < S → f c ≤ bst) ∧ (bst = 0 ∨ ∃ c, c < S ∧ f c = bst) ∧
          σ'.vars "acc" = min (σ.vars "acc" + (bst - 1)) C) ∧
        Tbl "V" S f σ' ∧ σ'.vars "S" = S ∧ σ'.vars "cap" = C ∧ σ'.vars "acc" ≤ C)
      (20 * S + 20) := by
  run_vcg [(bestLoop_spec (B := B) S f hS (fun c hc => by have := hf c hc; omega)).frame]
  all_goals have hSv : σ.vars "S" = S := ‹σ.vars "S" = S›
  all_goals have hT : Tbl "V" S f σ := ‹Tbl "V" S f σ›
  all_goals have hcap : σ.vars "cap" = C := ‹σ.vars "cap" = C›
  all_goals have hacc : σ.vars "acc" ≤ C := ‹σ.vars "acc" ≤ C›
  all_goals try
    (obtain ⟨⟨hT1, hS1, hub, hat⟩, hfv, hfa, -, -⟩ :=
      ‹_ ∧ (∀ y ∉ bestLoop.wvars, _) ∧ _›
     have hfcap := hfv "cap" (by simp [bestLoop, bestBody, Com.wvars])
     have hfacc := hfv "acc" (by simp [bestLoop, bestBody, Com.wvars])
     have hbstB : ∀ c, c < S → f c ≤ _ := hub)
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try omega
  all_goals first
    | (exact ⟨⟨_, hub, hat, by omega⟩, hT1, hS1, by omega, by omega⟩)
    | (rcases hat with h0 | ⟨c, hc, hfc⟩
       · omega
       · have := hf c hc; omega)
    | exact ⟨hSv, hT⟩
    | (rcases hat with h0 | ⟨c, hc, hfc⟩
       · omega
       · have := hf c hc
         omega)

/-- Letting time run, with the table read off the state. -/
theorem commitLoop_specG (m P S K : ℕ) (hS : (P + 1) ^ m ≤ S) (hmB : m + 2 < B)
    (hKB : K < B) :
    Spec B (fun σ => σ.vars "S" = S ∧ σ.vars "m" = m ∧ σ.vars "P" = P ∧
        S + P + σ.vars "del" + 2 < B ∧ Pw m P σ ∧ (σ.arrs "V").length = S ∧
        (∀ c, (σ.arrs "V").getD c 0 ≤ K) ∧ (σ.arrs "Vt").length = S ∧
        (σ.arrs "V2").length = S) commitLoop
      (fun σ σ' => Tbl "V" S
          (pushed P m (σ.vars "del") (fun c => (σ.arrs "V").getD c 0) S) σ' ∧
        Tbl "V2" S (pushed P m (σ.vars "del") (fun c => (σ.arrs "V").getD c 0) S) σ' ∧
        σ'.vars "S" = S) ((44 * m + 88) * S + 18) := by
  intro σ ⟨hSv, hm, hP, hdB, hpw, hlenV, hbnd, hlenVt, hlenV2⟩
  exact commitLoop_spec (B := B) m P (σ.vars "del") S K
    (fun c => (σ.arrs "V").getD c 0) hS hmB hdB (fun c => hbnd c) hKB σ
    ⟨hSv, hm, hP, rfl, hpw, ⟨hlenV, fun c _ => rfl⟩, hlenVt, hlenV2⟩

/-! ### What the passes write -/

lemma wvars_relaxLoop : relaxLoop.wvars = ["c", "u", "c2", "v", "c"] := by
  simp [relaxLoop, relaxBody, Com.wvars]

lemma warrs_relaxLoop : relaxLoop.warrs = ["V2"] := by
  simp [relaxLoop, relaxBody, Com.warrs]

lemma wvars_takeLoop : takeLoop.wvars = ["c", "c"] := by simp [takeLoop, takeBody, Com.wvars]

lemma warrs_takeLoop : takeLoop.warrs = ["V"] := by simp [takeLoop, takeBody, Com.warrs]

lemma wvars_commitLoop : ∀ y ∈ commitLoop.wvars, y ∈ ["c", "c2", "i", "u"] := by
  intro y hy
  simp only [commitLoop, shiftLoop, zeroLoop, zeroLoopOf, zeroBodyOf, shiftBody, advLoop,
    advBody, commitBody, Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hy ⊢
  tauto

lemma warrs_commitLoop : ∀ a ∈ commitLoop.warrs, a ∈ ["Vt", "V", "V2"] := by
  intro a ha
  simp only [commitLoop, shiftLoop, zeroLoop, zeroLoopOf, zeroBodyOf, shiftBody, advLoop,
    advBody, commitBody, Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at ha ⊢
  tauto

lemma wvars_closeBlock : ∀ y ∈ closeBlock.wvars, y ∈ ["bst", "c", "acc"] := by
  intro y hy
  simp only [closeBlock, bestLoop, bestBody, Com.wvars, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hy ⊢
  tauto

lemma warrs_closeBlock : closeBlock.warrs = [] := by
  simp [closeBlock, bestLoop, bestBody, Com.warrs]

lemma wvars_clearLoop : ∀ y ∈ clearLoop.wvars, y ∈ ["c", "tp"] := by
  intro y hy
  simp only [clearLoop, zeroLoopOf, zeroBodyOf, Com.wvars, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hy ⊢
  tauto

lemma warrs_clearLoop : ∀ a ∈ clearLoop.warrs, a ∈ ["V"] := by
  intro a ha
  simp only [clearLoop, zeroLoopOf, zeroBodyOf, Com.warrs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at ha ⊢
  tauto

end Lax470956Proofs.SweepTable
