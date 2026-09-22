import Lax470956Proofs.Construction1Read

/-!
Construction 1 as a word RAM program: the rank table and the edge table.
-/

namespace Lax470956Proofs.Construction1Tables

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.MulticolouredClique Lax470956.Construction1
open Lax470956Proofs.Construction1Shape Lax470956Proofs.Construction1Prog
open Lax470956Proofs.Construction1Read Lax470956Proofs.Construction1Rank
open Lax470956Proofs.Construction1Edges

variable {x : List ℕ} {G : Instance}

/-- What every later phase knows: the counts, the copied word, and where its parts
begin. -/
def Base (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = vn x ∧ σ.vars "m" = ve x ∧ σ.arrs "a" = body x ∧
    σ.vars "tb" = vn x + 1 ∧ σ.vars "cb" = vn x + 1 + 2 * ve x ∧
    σ.vars "k" = kk x ∧ σ.vars "nk" = vn x * kk x

/-! ### The rank table -/

/-- The sweep in progress: `cnt` vertices numbered, and every vertex whose turn has come
holds its rank. -/
def KInv (x : List ℕ) (σ : Env) : Prop :=
  Base x σ ∧ σ.out = [] ∧ Tables x σ ∧ σ.vars "i" ≤ vn x * kk x ∧
    σ.vars "cnt" = sweep (colr x) (vn x) (σ.vars "i") ∧
    ∀ v < vn x, colr x v * vn x + v < σ.vars "i" →
      (σ.arrs "r").getD v 0 = before (colr x) (vn x) v + 1

lemma sub_div_mul (i n : ℕ) : i - i / n * n = i % n := by
  have := Nat.div_add_mod' i n
  omega

lemma key_eq {n c v i : ℕ} (hv : v < n) (h : c * n + v = i) : v = i % n ∧ c = i / n := by
  subst h
  constructor
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv]; omega

lemma body_col' (x : List ℕ) (v : ℕ) :
    (body x)[vn x + 1 + 2 * ve x + v]?.getD 0 = colr x v := by
  rw [← List.getD_eq_getElem?_getD]; exact body_col x v

theorem rankBody_spec (hR : Reads x G) :
    Spec (bnd x G) (fun σ => KInv x σ ∧ σ.vars "i" < vn x * kk x) rankBody
      (fun σ σ' => KInv x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  refine Spec.pre (P := fun σ => KInv x σ ∧ σ.vars "i" < vn x * kk x ∧
      0 < vn x ∧ σ.vars "i" % vn x < vn x ∧ σ.vars "i" / vn x < kk x ∧
      σ.vars "i" - σ.vars "i" / vn x * vn x = σ.vars "i" % vn x ∧
      σ.vars "i" / vn x * vn x ≤ σ.vars "i" ∧
      σ.vars "i" + 1 < bnd x G ∧ σ.vars "cnt" + 1 < bnd x G ∧
      vn x + kk x < bnd x G ∧ (body x).length + 2 < bnd x G ∧
      (body x).length = 2 * vn x + 2 * ve x + 2 ∧
      (∀ j < (body x).length, (body x).getD j 0 < bnd x G)) ?_ ?_
  · run_vcg
    all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hout, ⟨hr, heu, hev⟩, hile, hcnt, hrk⟩ :=
      ‹KInv x σ›
    all_goals have hsub := ‹σ.vars "i" - σ.vars "i" / vn x * vn x = σ.vars "i" % vn x›
    all_goals have hblen := ‹(body x).length = 2 * vn x + 2 * ve x + 2›
    all_goals have hbB := ‹∀ j < (body x).length, (body x).getD j 0 < bnd x G›
    all_goals have hmod := ‹σ.vars "i" % vn x < vn x›
    all_goals have hi := ‹σ.vars "i" < vn x * kk x›
    all_goals try simp only [KInv, Base, Tables]
    · rename_i hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hr, hsub, body_col'] at hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hr, hsub]
      have hdm := Nat.div_add_mod' (σ.vars "i") (vn x)
      refine ⟨hout, ⟨heu, hev⟩, hi, by rw [hcnt, if_pos hc], ?_⟩
      intro v hv hle
      by_cases hv' : v = σ.vars "i" % vn x
      · subst hv'
        simp [hr, hmod]
        have h1 := sweep_eq (cf := colr x) (n := vn x) (σ.vars "i" / vn x)
          (σ.vars "i" % vn x) (by omega)
        rw [hdm] at h1
        rw [hcnt, h1, before_eq, hc, Nat.min_eq_right (by omega)]
      · rw [List.getElem?_set_ne (fun h => hv' h.symm)]
        refine hrk v hv (lt_of_le_of_ne hle fun heq => hv' (key_eq hv heq).1)
    · rename_i hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hr, hsub, body_col'] at hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hr, hsub]
      refine ⟨hout, ⟨heu, hev⟩, hi, by rw [hcnt, if_neg hc]; rfl, ?_⟩
      intro v hv hle
      refine hrk v hv (lt_of_le_of_ne hle fun heq => hc ?_)
      obtain ⟨h1, h2⟩ := key_eq hv heq
      rw [← h1, ← h2]
    all_goals try simp [hn, hm, ha, htb, hcb, hk, hnk, hr, hsub]
    all_goals try omega
    · have := hbB (vn x + 1 + 2 * ve x + σ.vars "i" % vn x) (by omega)
      rwa [List.getD_eq_getElem?_getD] at this
  · rintro σ ⟨hI, hi⟩
    have hpos : 0 < vn x := by
      rcases Nat.eq_zero_or_pos (vn x) with h | h
      · rw [h] at hi; simp at hi
      · exact h
    have hdm := Nat.div_add_mod' (σ.vars "i") (vn x)
    have hcnt : σ.vars "cnt" ≤ σ.vars "i" := by
      rw [hI.2.2.2.2.1, sweep]
      exact le_trans (List.length_filter_le _ _) (by simp)
    have h1 := nk_le_nJobs hR
    have h2 := nJobs_lt_bnd (x := x) (G := G)
    have h3 := small_lt_bnd hR
    have h5 := len_lt_bnd (x := x) (G := G)
    have h6 : (body x).length ≤ x.length := by simp [body]
    refine ⟨hI, hi, hpos, Nat.mod_lt _ hpos, (Nat.div_lt_iff_lt_mul hpos).mpr (by
      rw [Nat.mul_comm]; exact hi), sub_div_mul _ _, Nat.div_mul_le_self _ _,
      by omega, by omega, by omega, by omega, body_length hR,
      fun j hj => body_entry_lt j hj⟩

/-- The sweep fills the rank table. -/
theorem rankLoop_spec (hR : Reads x G) :
    Spec (bnd x G) (fun σ => KInv x (σ.setVar "i" 0)) rankLoop
      (fun _ σ' => KInv x σ' ∧ σ'.vars "i" = vn x * kk x)
      (44 * (vn x * kk x) + 6) :=
  Spec.forRangeZero "i" "nk" (KInv x) (vn x * kk x) 40
    (by have h1 := nk_le_nJobs hR; have h2 := nJobs_lt_bnd (x := x) (G := G); omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.1.2.2.2.2.2.2) (rankBody_spec hR)

/-! ### The edge table -/

/-- The rank table, filled. -/
def Ranked (x : List ℕ) (σ : Env) : Prop :=
  (σ.arrs "r").length = vn x ∧
    ∀ v < vn x, (σ.arrs "r").getD v 0 = before (colr x) (vn x) v + 1

/-- The scan in progress: the owner pointer `u` has caught up with the slot pointer `p`,
and the two tables hold the pairs kept so far. -/
def EInv (x : List ℕ) (σ : Env) : Prop :=
  Base x σ ∧ σ.out = [] ∧ Ranked x σ ∧ σ.vars "S" = vn x + 2 * ve x ∧
    σ.vars "i" = σ.vars "u" + σ.vars "p" ∧ σ.vars "u" ≤ vn x ∧
    off x (σ.vars "u") ≤ σ.vars "p" ∧ σ.vars "p" ≤ 2 * ve x ∧
    σ.vars "E" = (acc x (σ.vars "p")).length ∧
    (σ.arrs "eu").length = 2 * ve x ∧ (σ.arrs "ev").length = 2 * ve x ∧
    (σ.arrs "eu").take (σ.vars "E") = (acc x (σ.vars "p")).map Prod.fst ∧
    (σ.arrs "ev").take (σ.vars "E") = (acc x (σ.vars "p")).map Prod.snd

lemma body_off' (x : List ℕ) (i : ℕ) : (body x)[i]?.getD 0 = off x i := by
  rw [← List.getD_eq_getElem?_getD]; exact body_off x i

lemma take_succ_set {l : List ℕ} {e a : ℕ} (h : e < l.length) :
    (l.set e a).take (e + 1) = l.take e ++ [a] := by
  rw [List.take_succ, List.take_set_of_le (le_refl _)]
  simp [h]

lemma acc_length_le (x : List ℕ) (p : ℕ) : (acc x p).length ≤ p := by
  rw [acc, List.length_map]
  exact le_trans (List.length_filter_le _ _) (by simp)

@[simp] lemma off_tgt (x : List ℕ) (t : ℕ) : off x (vn x + 1 + t) = tgt x t := by
  rw [← body_off, body_tgt]

@[simp] lemma off_col (x : List ℕ) (v : ℕ) : off x (vn x + 1 + 2 * ve x + v) = colr x v := by
  rw [← body_off, body_col]

/-- The bounds on what the program reads out of the copied word. -/
def ReadsB (x : List ℕ) (G : Instance) : Prop :=
  (∀ i ≤ vn x, off x i < bnd x G) ∧ (∀ t < 2 * ve x, tgt x t < bnd x G) ∧
    (∀ v < vn x, colr x v < bnd x G) ∧ (body x).length + 2 < bnd x G ∧
    (body x).length = 2 * vn x + 2 * ve x + 2

lemma readsB (hR : Reads x G) : ReadsB x G := by
  have hlen := body_length hR
  have h5 := len_lt_bnd (x := x) (G := G)
  have h6 : (body x).length ≤ x.length := by simp [body]
  refine ⟨fun i hi => ?_, fun t ht => ?_, fun v hv => ?_, by omega, hlen⟩
  · rw [← body_off]; exact body_entry_lt _ (by omega)
  · rw [← body_tgt]; exact body_entry_lt _ (by omega)
  · rw [← body_col]; exact body_entry_lt _ (by omega)

theorem edgeBody_spec (hR : Reads x G) :
    Spec (bnd x G) (fun σ => EInv x σ ∧ σ.vars "i" < vn x + 2 * ve x) edgeBody
      (fun σ σ' => EInv x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 60 := by
  refine Spec.pre (P := fun σ => EInv x σ ∧ σ.vars "i" < vn x + 2 * ve x ∧
      σ.vars "u" < vn x ∧ σ.vars "E" ≤ σ.vars "p" ∧
      (σ.vars "p" < off x (σ.vars "u" + 1) →
        σ.vars "p" < 2 * ve x ∧ tgt x (σ.vars "p") < vn x ∧
          own x (σ.vars "p") = σ.vars "u") ∧ ReadsB x G) ?_ ?_
  · run_vcg
    all_goals obtain ⟨⟨hn, hm, ha, htb, hcb, hk, hnk⟩, hout, hrk, hS, hiup, hun, hoff, hp2,
      hE, heu, hev, htu, htv⟩ := ‹EInv x σ›
    all_goals obtain ⟨hoffB, htgtB, hcolB, hlenB, hblen⟩ := ‹ReadsB x G›
    all_goals have hslot := ‹σ.vars "p" < off x (σ.vars "u" + 1) → _›
    all_goals have hu := ‹σ.vars "u" < vn x›
    all_goals try (have hs := hslot (by
      have h := ‹σ.vars "p" < (σ.arrs "a").getD (σ.vars "u" + 1) 0›
      rw [ha, body_off] at h; exact h))
    all_goals try simp only [EInv, Base, Ranked]
    · rename_i hc1 hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hS, body_off'] at hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hS, body_off']
      obtain ⟨hs1, hs2, hs3⟩ := hs
      have hacc : acc x (σ.vars "p" + 1) = acc x (σ.vars "p")
          ++ [(σ.vars "u", tgt x (σ.vars "p"))] := by
        rw [acc_succ, hs3, if_pos hc]
      have hEl : σ.vars "E" < 2 * ve x := by omega
      refine ⟨hout, hrk, by omega, by omega, by omega, hs1, ?_, heu, hev, ?_, ?_⟩
      · rw [hacc, List.length_append, ← hE]; rfl
      · rw [take_succ_set (by rw [heu]; exact hEl), htu, hacc]; simp
      · rw [take_succ_set (by rw [hev]; exact hEl), htv, hacc]; simp
    · rename_i hc1 hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hS, body_off'] at hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hS, body_off']
      obtain ⟨hs1, hs2, hs3⟩ := hs
      have hacc : acc x (σ.vars "p" + 1) = acc x (σ.vars "p") := by
        rw [acc_succ, hs3, if_neg (by omega)]; simp
      rw [hacc]
      exact ⟨hout, hrk, by omega, by omega, by omega, hs1, hE, heu, hev, htu, htv⟩
    · rename_i hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hS, body_off'] at hc
      simp [hn, hm, ha, htb, hcb, hk, hnk, hS, body_off']
      exact ⟨hout, hrk, by omega, hu, hc, hp2, hE, heu, hev, htu, htv⟩
    all_goals try simp [hn, hm, ha, htb, hcb, hk, hnk, hS, body_off']
    all_goals try omega
    all_goals try (first
      | (apply hoffB; omega) | (apply htgtB; omega) | (apply hcolB; omega))
  · rintro σ ⟨hI, hi⟩
    have hI' := hI
    obtain ⟨hB, hout, hrk, hS, hiup, hun, hoff, hp2, hE, -⟩ := hI
    have hu : σ.vars "u" < vn x := by
      rcases Nat.lt_or_ge (σ.vars "u") (vn x) with h | h
      · exact h
      · have hue : σ.vars "u" = vn x := by omega
        rw [hue, hR.off_last] at hoff
        omega
    refine ⟨hI', hi, hu, by rw [hE]; exact acc_length_le _ _, fun hlt => ?_, readsB hR⟩
    have hlast := off_mono hR (i := σ.vars "u" + 1) (j := vn x) (by omega) (le_refl _)
    rw [hR.off_last] at hlast
    have hp : σ.vars "p" < 2 * ve x := by omega
    exact ⟨hp, hR.tgt_lt _ hp, own_eq hR hu hoff hlt⟩

/-- The scan fills the edge table. -/
theorem edgeLoop_spec (hR : Reads x G) :
    Spec (bnd x G) (fun σ => EInv x (σ.setVar "i" 0)) edgeLoop
      (fun _ σ' => EInv x σ' ∧ σ'.vars "i" = vn x + 2 * ve x)
      (64 * (vn x + 2 * ve x) + 6) :=
  Spec.forRangeZero "i" "S" (EInv x) (vn x + 2 * ve x) 60
    (by have := (readsB hR).2.2.2.1; have := (readsB hR).2.2.2.2; omega)
    (fun σ h => by
      obtain ⟨-, -, -, -, hiup, hun, -, hp2, -⟩ := h
      omega)
    (fun _ h => h.2.2.2.1) (edgeBody_spec hR)

end Lax470956Proofs.Construction1Tables
