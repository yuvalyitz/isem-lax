import Lax470956Proofs.SweepPre

/-!
The order pass: walking the blocks and writing the jobs out in the order the sweep wants
them.

The pass has three nested loops. The outer one runs over the jobs and opens a block at
the job that closes its first deadline; the middle one walks the block's deadlines; the
inner one writes out the jobs of one deadline. What the three of them leave behind is
the `Order` contract of `SweepLoop`.
-/

namespace Lax470956Proofs.SweepOrder

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax470956.Scheduling Lax470956.Scheduling.Instance
open Lax470956.InstanceEncoding
open Lax470956Proofs.BlockWalk
open Lax470956Proofs.SweepProg Lax470956Proofs.SweepTable Lax470956Proofs.SweepBody
open Lax470956Proofs.SweepPre

variable {B : ℕ} {x : List ℕ} {n P M Lo : ℕ} {occ : ℕ → Bool}

/-! ### The list of jobs at one deadline -/

lemma jlist_tail {f : ℕ → ℕ} {d : ℕ} : ∀ N a l, jlist f d N = a :: l → l = jlist f d a := by
  intro N
  induction N with
  | zero => intro a l h; simp [jlist] at h
  | succ N ih =>
      intro a l h
      rw [jlist] at h
      split at h
      · rw [List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · exact ih a l h

lemma hd1_eq_zero_iff {l : List ℕ} : hd1 l = 0 ↔ l = [] := by
  cases l <;> simp [hd1]

lemma jlist_head {f : ℕ → ℕ} {d N : ℕ} (h : hd1 (jlist f d N) ≠ 0) :
    jlist f d N = (hd1 (jlist f d N) - 1) :: jlist f d (hd1 (jlist f d N) - 1) := by
  rcases hl : jlist f d N with _ | ⟨a, l⟩
  · rw [hl] at h; simp [hd1] at h
  · have hjt := jlist_tail N a l hl
    simp only [hd1, Nat.add_sub_cancel]
    rw [← hjt]

/-! ### Which block a position belongs to -/

/-- How many block starts there are up to and including `k`. -/
def blkA (σ : Env) (k : ℕ) : ℕ := ∑ t ∈ Finset.range (k + 1), (σ.arrs "nc").getD t 0

lemma blkA_succ (σ : Env) (k : ℕ) :
    blkA σ (k + 1) = blkA σ k + (σ.arrs "nc").getD (k + 1) 0 := by
  simp [blkA, Finset.sum_range_succ]

lemma blkA_mono (σ : Env) {a b : ℕ} (h : a ≤ b) : blkA σ a ≤ blkA σ b := by
  simp only [blkA]
  exact Finset.sum_le_sum_of_subset (by
    intro y hy; simp only [Finset.mem_range] at hy ⊢; omega)

lemma blkA_pred (σ : Env) (kk : ℕ) :
    ∑ t ∈ Finset.range kk, (σ.arrs "nc").getD t 0
      = if kk = 0 then 0 else blkA σ (kk - 1) := by
  cases kk with
  | zero => simp
  | succ k => simp [blkA]

lemma blkA_congr {σ σ' : Env} {k : ℕ}
    (h : ∀ t, t ≤ k → (σ'.arrs "nc").getD t 0 = (σ.arrs "nc").getD t 0) :
    blkA σ' k = blkA σ k := by
  simp only [blkA]
  refine Finset.sum_congr rfl fun t ht => h t ?_
  have := Finset.mem_range.mp ht
  omega

/-! ### What the pass reads and what it has built -/

/-- The arrays the four earlier passes left behind. -/
structure Src (x : List ℕ) (n P Lo : ℕ) (σ : Env) : Prop where
  arrA : σ.arrs "a" = x
  varn : σ.vars "n" = n
  fjv : ∀ d, (σ.arrs "fj").getD d 0 = hd1 (jlist (due x) d n)
  njv : ∀ j, j < n → (σ.arrs "nj").getD j 0 = hd1 (jlist (due x) (due x j) j)
  stv : ∀ d, occB x n d = true →
    (σ.arrs "st").getD d 0 = (if isStart P (occB x n) d then 1 else 0)
  nx2v : ∀ d, occB x n d = true → (σ.arrs "nx2").getD d 0 = nxt P (occB x n) d
  lord : n ≤ (σ.arrs "ord").length
  ldl : n ≤ (σ.arrs "dl").length
  lnc : n ≤ (σ.arrs "nc").length
  lnj : n ≤ (σ.arrs "nj").length
  lfj : Lo ≤ (σ.arrs "fj").length
  lst : Lo ≤ (σ.arrs "st").length
  lnx2 : Lo ≤ (σ.arrs "nx2").length

/-- The order the pass has written out so far, with `Em` the jobs it has written. -/
structure OInv (x : List ℕ) (P n : ℕ) (Em : ℕ → Prop) (σ : Env) : Prop where
  kkn : σ.vars "kk" ≤ n
  lt : ∀ k, k < σ.vars "kk" → (σ.arrs "ord").getD k 0 < n
  dle : ∀ k, k < σ.vars "kk" → (σ.arrs "dl").getD k 0 = due x ((σ.arrs "ord").getD k 0)
  nc01 : ∀ k, k < σ.vars "kk" → (σ.arrs "nc").getD k 0 ≤ 1
  cov : ∀ j, j < n → ((∃ k, k < σ.vars "kk" ∧ (σ.arrs "ord").getD k 0 = j) ↔ Em j)
  inj : ∀ a b, a < σ.vars "kk" → b < σ.vars "kk" →
    (σ.arrs "ord").getD a 0 = (σ.arrs "ord").getD b 0 → a = b
  cut0 : 0 < σ.vars "kk" → (σ.arrs "nc").getD 0 0 = 1
  mono : ∀ k, 0 < k → k < σ.vars "kk" → (σ.arrs "nc").getD k 0 = 0 →
    (σ.arrs "dl").getD (k - 1) 0 ≤ (σ.arrs "dl").getD k 0
  sep : ∀ a b, a < σ.vars "kk" → b < σ.vars "kk" → blkA σ a ≠ blkA σ b →
    (σ.arrs "dl").getD a 0 + P ≤ (σ.arrs "dl").getD b 0 ∨
      (σ.arrs "dl").getD b 0 + P ≤ (σ.arrs "dl").getD a 0

/-- The index of the block the next job written out will belong to. -/
def nb (σ : Env) : ℕ :=
  (if σ.vars "kk" = 0 then 0 else blkA σ (σ.vars "kk" - 1)) + σ.vars "nc0"

/-- The pass, inside a block whose first deadline is `s`. -/
structure BInvO (x : List ℕ) (P n M s : ℕ) (σ : Env) : Prop where
  nc0le : σ.vars "nc0" ≤ 1
  first : σ.vars "kk" = 0 → σ.vars "nc0" = 1
  curIn : σ.vars "cur" ∈ chain P (occB x n) M s
  prevle : 0 < σ.vars "kk" → σ.vars "nc0" = 0 →
    (σ.arrs "dl").getD (σ.vars "kk" - 1) 0 ≤ σ.vars "cur"
  sepcur : ∀ a, a < σ.vars "kk" → blkA σ a ≠ nb σ →
    ∀ d, d ∈ chain P (occB x n) M s →
      (σ.arrs "dl").getD a 0 + P ≤ d ∨ d + P ≤ (σ.arrs "dl").getD a 0

/-- The jobs written out: those of finished deadlines, and those of the deadline in hand
from `r` up. -/
def EmAt (x : List ℕ) (Dn : ℕ → Prop) (cur r : ℕ) : ℕ → Prop :=
  fun j => Dn (due x j) ∨ (due x j = cur ∧ r ≤ j)

/-! ### Writing out one job -/

variable {Dn : ℕ → Prop} {s r : ℕ}

/-- Room is left: a job that has not been written out yet bounds `kk` away from `n`. -/
lemma kk_lt_of_fresh {Em : ℕ → Prop} {σ : Env} (h : OInv x P n Em σ) {a : ℕ}
    (han : a < n) (hfresh : ¬ Em a) : σ.vars "kk" < n := by
  classical
  have hinj : ∀ k₁ ∈ Finset.range (σ.vars "kk"), ∀ k₂ ∈ Finset.range (σ.vars "kk"),
      (σ.arrs "ord").getD k₁ 0 = (σ.arrs "ord").getD k₂ 0 → k₁ = k₂ := by
    intro k₁ h1 k₂ h2 he
    exact h.inj k₁ k₂ (Finset.mem_range.mp h1) (Finset.mem_range.mp h2) he
  have hmaps : ∀ k ∈ Finset.range (σ.vars "kk"),
      (σ.arrs "ord").getD k 0 ∈ (Finset.range n).erase a := by
    intro k hk
    have hklt := Finset.mem_range.mp hk
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr (h.lt k hklt)⟩
    intro hc
    exact hfresh ((h.cov a han).mp ⟨k, hklt, hc⟩)
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range, Finset.card_erase_of_mem (Finset.mem_range.mpr han),
    Finset.card_range] at hcard
  omega

theorem emitStep_spec (M : ℕ) (hn : n + 2 < B) (cur : ℕ)
    (hcB : cur + 2 < B) (hrn : r ≤ n) (hDn : ¬ Dn cur) :
    Spec B (fun σ => Src x n P Lo σ ∧ BInvO x P n M s σ ∧
        OInv x P n (EmAt x Dn cur r) σ ∧ σ.vars "cur" = cur ∧
        σ.vars "jp" = hd1 (jlist (due x) cur r) ∧ 0 < σ.vars "jp") emitStep
      (fun σ σ' => Src x n P Lo σ' ∧ BInvO x P n M s σ' ∧
        OInv x P n (EmAt x Dn cur (σ.vars "jp" - 1)) σ' ∧ σ'.vars "cur" = cur ∧
        σ'.vars "jp" = hd1 (jlist (due x) cur (σ.vars "jp" - 1)) ∧
        σ'.vars "kk" = σ.vars "kk" + 1) 22 := by
  intro σ ⟨hsrc, hbin, hoin, hcur, hjp, hjp0⟩
  set kk := σ.vars "kk" with hkkdef
  set a := σ.vars "jp" - 1 with hadef
  have hlist : jlist (due x) cur r = a :: jlist (due x) cur a := by
    rw [hadef, hjp]; exact jlist_head (by omega)
  have hmem : a ∈ jlist (due x) cur r := by rw [hlist]; exact List.mem_cons_self
  obtain ⟨har, hdua⟩ := (jlist_mem (due x) cur r a).mp hmem
  have han : a < n := by omega
  have hfresh : ¬ EmAt x Dn cur r a := by
    simp only [EmAt, hdua, not_or]
    exact ⟨hDn, fun hc => by omega⟩
  have hkk : kk < n := kk_lt_of_fresh hoin han hfresh
  have hnj : (σ.arrs "nj").getD a 0 = hd1 (jlist (due x) cur a) := by
    rw [hsrc.njv a han, hdua]
  have hnjle : (σ.arrs "nj").getD a 0 ≤ a := by rw [hnj]; exact hd1_le _ _ _
  have hnc0 : σ.vars "nc0" ≤ 1 := hbin.nc0le
  have hordL : n ≤ (σ.arrs "ord").length := hsrc.lord
  have hdlL : n ≤ (σ.arrs "dl").length := hsrc.ldl
  have hncL : n ≤ (σ.arrs "nc").length := hsrc.lnc
  have hnjL : n ≤ (σ.arrs "nj").length := hsrc.lnj
  -- the six steps
  have e1 : (sub (V "jp") (lit 1)).evalB B σ = some a :=
    SweepBody.evalB_sub (SweepBody.evalB_var (by omega)) (SweepBody.evalB_lit (by omega))
      (by omega)
  refine ⟨((((σ.setArr "ord" kk a).setArr "dl" kk cur).setArr "nc" kk
      (σ.vars "nc0")).setVar "nc0" 0).setVar "jp" (hd1 (jlist (due x) cur a))
      |>.setVar "kk" (kk + 1), ?_, ?_⟩
  · refine ((Run.store (SweepBody.evalB_var (B := B) (by omega)) e1 (by omega)).seq
      ((Run.store (SweepBody.evalB_var (B := B) (by simp [Env.setArr]; omega))
          (by rw [← hcur]; exact SweepBody.evalB_var (by simp [Env.setArr]; omega))
          (by simp [Env.setArr]; omega)).seq
        ((Run.store (SweepBody.evalB_var (B := B) (by simp [Env.setArr]; omega))
            (SweepBody.evalB_var (by simp [Env.setArr]; omega))
            (by simp [Env.setArr]; omega)).seq
          ((Run.assign (SweepBody.evalB_lit (B := B) (by omega))).seq
            ((Run.assign (SweepBody.evalB_getE (B := B)
                (e := sub (V "jp") (lit 1)) (by simpa [Env.setVar, Env.setArr] using e1)
                (show hd1 (jlist (due x) cur a) < B by
                  have := hd1_le (due x) cur a; omega)
                (by simp [Env.setVar, Env.setArr]; omega)
                (by simpa [Env.setVar, Env.setArr] using hnj))).seq
              (Run.assign (SweepBody.evalB_add (SweepBody.evalB_var (by
                  simp [Env.setVar, Env.setArr]; omega))
                (SweepBody.evalB_lit (by omega))
                (by simp [Env.setVar, Env.setArr]; omega)))))))).mono ?_
    norm_num [Expr.size]
  · set τ := (((((σ.setArr "ord" kk a).setArr "dl" kk cur).setArr "nc" kk
        (σ.vars "nc0")).setVar "nc0" 0).setVar "jp"
        (hd1 (jlist (due x) cur a))).setVar "kk" (kk + 1) with hτ
    have tkk : τ.vars "kk" = kk + 1 := by simp [hτ, Env.setVar]
    have tjp : τ.vars "jp" = hd1 (jlist (due x) cur a) := by simp [hτ, Env.setVar]
    have tnc0 : τ.vars "nc0" = 0 := by simp [hτ, Env.setVar]
    have tcur : τ.vars "cur" = cur := by simp [hτ, Env.setVar, Env.setArr, hcur]
    have tn : τ.vars "n" = σ.vars "n" := by simp [hτ, Env.setVar, Env.setArr]
    have tord : τ.arrs "ord" = (σ.arrs "ord").set kk a := by
      simp [hτ, Env.setVar, Env.setArr]
    have tdl : τ.arrs "dl" = (σ.arrs "dl").set kk cur := by simp [hτ, Env.setVar, Env.setArr]
    have tnc : τ.arrs "nc" = (σ.arrs "nc").set kk (σ.vars "nc0") := by
      simp [hτ, Env.setVar, Env.setArr]
    have tA : τ.arrs "a" = σ.arrs "a" := by simp [hτ, Env.setVar, Env.setArr]
    have tfj : τ.arrs "fj" = σ.arrs "fj" := by simp [hτ, Env.setVar, Env.setArr]
    have tnj : τ.arrs "nj" = σ.arrs "nj" := by simp [hτ, Env.setVar, Env.setArr]
    have tst : τ.arrs "st" = σ.arrs "st" := by simp [hτ, Env.setVar, Env.setArr]
    have tnx2 : τ.arrs "nx2" = σ.arrs "nx2" := by simp [hτ, Env.setVar, Env.setArr]
    have tordk : ∀ k, k < kk → (τ.arrs "ord").getD k 0 = (σ.arrs "ord").getD k 0 := by
      intro k hk; rw [tord, getD_set_other (by omega)]
    have tdlk : ∀ k, k < kk → (τ.arrs "dl").getD k 0 = (σ.arrs "dl").getD k 0 := by
      intro k hk; rw [tdl, getD_set_other (by omega)]
    have tnck : ∀ k, k < kk → (τ.arrs "nc").getD k 0 = (σ.arrs "nc").getD k 0 := by
      intro k hk; rw [tnc, getD_set_other (by omega)]
    have tordkk : (τ.arrs "ord").getD kk 0 = a := by
      rw [tord, getD_set_self (by omega)]
    have tdlkk : (τ.arrs "dl").getD kk 0 = cur := by rw [tdl, getD_set_self (by omega)]
    have tnckk : (τ.arrs "nc").getD kk 0 = σ.vars "nc0" := by
      rw [tnc, getD_set_self (by omega)]
    have tblk : ∀ k, k < kk → blkA τ k = blkA σ k := fun k hk =>
      blkA_congr fun t ht => tnck t (by omega)
    have tblkkk : blkA τ kk = nb σ := by
      have h1 : ∑ t ∈ Finset.range kk, (τ.arrs "nc").getD t 0
          = ∑ t ∈ Finset.range kk, (σ.arrs "nc").getD t 0 :=
        Finset.sum_congr rfl fun t ht => tnck t (Finset.mem_range.mp ht)
      rw [blkA, Finset.sum_range_succ, h1, blkA_pred, nb, tnckk]
    have tnb : nb τ = nb σ := by
      rw [nb, tkk, tnc0, if_neg (by omega)]
      simpa using tblkkk
    refine ⟨⟨by rw [tA]; exact hsrc.arrA, by rw [tn]; exact hsrc.varn,
      by rw [tfj]; exact hsrc.fjv, by rw [tnj]; exact hsrc.njv,
      by rw [tst]; exact hsrc.stv, by rw [tnx2]; exact hsrc.nx2v,
      by rw [tord, List.length_set]; exact hsrc.lord,
      by rw [tdl, List.length_set]; exact hsrc.ldl,
      by rw [tnc, List.length_set]; exact hsrc.lnc,
      by rw [tnj]; exact hsrc.lnj, by rw [tfj]; exact hsrc.lfj,
      by rw [tst]; exact hsrc.lst, by rw [tnx2]; exact hsrc.lnx2⟩,
      ⟨by rw [tnc0]; omega, by rw [tkk]; omega, by rw [tcur, ← hcur]; exact hbin.curIn,
        ?_, ?_⟩, ⟨by rw [tkk]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      tcur, tjp, tkk⟩
    · intro _ _; rw [tkk, tcur, Nat.add_sub_cancel, tdlkk]
    · intro a' ha' hne d hd
      rw [tkk] at ha'
      rcases Nat.lt_or_ge a' kk with hlt | hge
      · rw [tdlk a' hlt]
        exact hbin.sepcur a' hlt (by rw [← tblk a' hlt, ← tnb]; exact hne) d hd
      · exfalso
        have : a' = kk := by omega
        subst this
        exact hne (by rw [tblkkk, tnb])
    · intro k hk
      rw [tkk] at hk
      rcases Nat.lt_or_ge k kk with hlt | hge
      · rw [tordk k hlt]; exact hoin.lt k hlt
      · rw [show k = kk from by omega, tordkk]; exact han
    · intro k hk
      rw [tkk] at hk
      rcases Nat.lt_or_ge k kk with hlt | hge
      · rw [tordk k hlt, tdlk k hlt]; exact hoin.dle k hlt
      · rw [show k = kk from by omega, tordkk, tdlkk, hdua]
    · intro k hk
      rw [tkk] at hk
      rcases Nat.lt_or_ge k kk with hlt | hge
      · rw [tnck k hlt]; exact hoin.nc01 k hlt
      · rw [show k = kk from by omega, tnckk]; exact hnc0
    · intro j hjn
      rw [tkk]
      constructor
      · rintro ⟨k, hk, hkj⟩
        rcases Nat.lt_or_ge k kk with hlt | hge
        · rw [tordk k hlt] at hkj
          have := (hoin.cov j hjn).mp ⟨k, hlt, hkj⟩
          simp only [EmAt] at this ⊢
          rcases this with h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, by omega⟩
        · rw [show k = kk from by omega, tordkk] at hkj
          subst hkj
          exact Or.inr ⟨hdua, le_refl a⟩
      · intro hj
        simp only [EmAt] at hj
        by_cases hja : j = a
        · exact ⟨kk, by omega, by rw [tordkk, hja]⟩
        · have hEm : EmAt x Dn cur r j := by
            simp only [EmAt]
            rcases hj with h | ⟨h1, h2⟩
            · exact Or.inl h
            · refine Or.inr ⟨h1, ?_⟩
              by_contra hc
              have hjmem : j ∈ jlist (due x) cur r :=
                (jlist_mem (due x) cur r j).mpr ⟨by omega, h1⟩
              rw [hlist, List.mem_cons] at hjmem
              rcases hjmem with rfl | hm
              · exact hja rfl
              · have := (jlist_mem (due x) cur a j).mp hm
                omega
          obtain ⟨k, hk, hkj⟩ := (hoin.cov j hjn).mpr hEm
          exact ⟨k, by omega, by rw [tordk k hk]; exact hkj⟩
    · intro a' b' ha' hb' he
      rw [tkk] at ha' hb'
      rcases Nat.lt_or_ge a' kk with hla | hga <;> rcases Nat.lt_or_ge b' kk with hlb | hgb
      · rw [tordk a' hla, tordk b' hlb] at he; exact hoin.inj a' b' hla hlb he
      · exfalso
        rw [tordk a' hla, show b' = kk from by omega, tordkk] at he
        exact hfresh ((hoin.cov a han).mp ⟨a', hla, he⟩)
      · exfalso
        rw [tordk b' hlb, show a' = kk from by omega, tordkk] at he
        exact hfresh ((hoin.cov a han).mp ⟨b', hlb, he.symm⟩)
      · omega
    · intro _
      rcases Nat.eq_zero_or_pos kk with h0 | hpos
      · rw [tnc, h0, getD_set_self (by omega)]
        exact hbin.first h0
      · rw [tnck 0 hpos]; exact hoin.cut0 hpos
    · intro k hk0 hk hnc
      rw [tkk] at hk
      rcases Nat.lt_or_ge k kk with hlt | hge
      · rw [tdlk (k - 1) (by omega), tdlk k hlt]
        exact hoin.mono k hk0 hlt (by rw [← tnck k hlt]; exact hnc)
      · have hkeq : k = kk := by omega
        rw [hkeq] at hnc ⊢
        rw [tnckk] at hnc
        rw [tdlk (kk - 1) (by omega), tdlkk, ← hcur]
        exact hbin.prevle (by omega) hnc
    · intro a' b' ha' hb' hne
      rw [tkk] at ha' hb'
      rcases Nat.lt_or_ge a' kk with hla | hga <;> rcases Nat.lt_or_ge b' kk with hlb | hgb
      · rw [tdlk a' hla, tdlk b' hlb]
        exact hoin.sep a' b' hla hlb (by rw [← tblk a' hla, ← tblk b' hlb]; exact hne)
      · have hbeq : b' = kk := by omega
        subst hbeq
        rw [tdlk a' hla, tdlkk]
        refine hbin.sepcur a' hla ?_ cur ?_
        · rw [← tblk a' hla, ← tblkkk]; exact hne
        · rw [← hcur]; exact hbin.curIn
      · have haeq : a' = kk := by omega
        subst haeq
        rw [tdlk b' hlb, tdlkk]
        rcases hbin.sepcur b' hlb (by rw [← tblk b' hlb, ← tblkkk]; exact hne.symm) cur
          (by rw [← hcur]; exact hbin.curIn) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · exact absurd (show a' = b' from by omega) (by rintro rfl; exact hne rfl)

/-! ### Writing out every job of one deadline -/

lemma evalB_lt0 {σ : Env} {y : String} (h0 : 0 < B) (h : σ.vars y < B) :
    (Cond.lt (lit 0) (V y)).evalB B σ = some (decide (0 < σ.vars y)) := by
  simp [Cond.evalB, Expr.evalB, fit_self h0, fit_self h]

/-- The potential the order pass runs on: the jobs still to be written out. -/
def Psi (n : ℕ) (σ : Env) : ℕ := 26 * (n - σ.vars "kk")

/-- The state of the innermost loop. -/
def EInvO (x : List ℕ) (P n Lo M s : ℕ) (Dn : ℕ → Prop) (cur kk0 : ℕ) (σ : Env) : Prop :=
  Src x n P Lo σ ∧ BInvO x P n M s σ ∧ σ.vars "cur" = cur ∧
    ∃ r, r ≤ n ∧ σ.vars "jp" = hd1 (jlist (due x) cur r) ∧
      OInv x P n (EmAt x Dn cur r) σ ∧
      σ.vars "kk" + (jlist (due x) cur r).length = kk0 + (jlist (due x) cur n).length

lemma OInv.congrEm {Em Em' : ℕ → Prop} {σ : Env} (h : OInv x P n Em σ)
    (he : ∀ j, j < n → (Em j ↔ Em' j)) : OInv x P n Em' σ :=
  { h with cov := fun j hj => (h.cov j hj).trans (he j hj) }

lemma Src.setV {σ : Env} (h : Src x n P Lo σ) {y : String} (hy : y ≠ "n") (v : ℕ) :
    Src x n P Lo (σ.setVar y v) :=
  { h with varn := by simp only [Env.setVar, if_neg hy.symm]; exact h.varn }

lemma BInvO.setV {σ : Env} {s : ℕ} (h : BInvO x P n M s σ) {y : String}
    (h1 : y ≠ "nc0") (h2 : y ≠ "kk") (h3 : y ≠ "cur") (v : ℕ) :
    BInvO x P n M s (σ.setVar y v) := by
  have e0 : (σ.setVar y v).vars "nc0" = σ.vars "nc0" := by
    simp only [Env.setVar, if_neg h1.symm]
  have e1 : (σ.setVar y v).vars "kk" = σ.vars "kk" := by
    simp only [Env.setVar, if_neg h2.symm]
  have e2 : (σ.setVar y v).vars "cur" = σ.vars "cur" := by
    simp only [Env.setVar, if_neg h3.symm]
  have e3 : ∀ k, blkA (σ.setVar y v) k = blkA σ k := fun k => blkA_congr fun t _ => rfl
  have e4 : nb (σ.setVar y v) = nb σ := by rw [nb, nb, e0, e1, e3]
  exact { nc0le := by rw [e0]; exact h.nc0le
          first := by rw [e0, e1]; exact h.first
          curIn := by rw [e2]; exact h.curIn
          prevle := by rw [e0, e1, e2]; exact h.prevle
          sepcur := by rw [e1, e4]; simpa [e3] using h.sepcur }

lemma OInv.setV {Em : ℕ → Prop} {σ : Env} (h : OInv x P n Em σ) {y : String}
    (h2 : y ≠ "kk") (v : ℕ) : OInv x P n Em (σ.setVar y v) := by
  have e1 : (σ.setVar y v).vars "kk" = σ.vars "kk" := by
    simp only [Env.setVar, if_neg h2.symm]
  have e3 : ∀ k, blkA (σ.setVar y v) k = blkA σ k := fun k => blkA_congr fun t _ => rfl
  exact { kkn := by rw [e1]; exact h.kkn
          lt := by rw [e1]; exact h.lt
          dle := by rw [e1]; exact h.dle
          nc01 := by rw [e1]; exact h.nc01
          cov := by rw [e1]; exact h.cov
          inj := by rw [e1]; exact h.inj
          cut0 := by rw [e1]; exact h.cut0
          mono := by rw [e1]; exact h.mono
          sep := by rw [e1]; simpa [e3] using h.sep }

theorem emitLoop_run (M : ℕ) (hn : n + 2 < B) (cur : ℕ) (hcB : cur + 2 < B)
    (hDn : ¬ Dn cur) (hocc : occB x n cur = true)
    (hdLo : ∀ d, occB x n d = true → d < Lo) (σ : Env)
    (hsrc : Src x n P Lo σ) (hbin : BInvO x P n M s σ)
    (hoin : OInv x P n (fun j => Dn (due x j)) σ) (hcur : σ.vars "cur" = cur) :
    ∃ σ' K, Run B emitLoop σ σ' K ∧ Src x n P Lo σ' ∧ BInvO x P n M s σ' ∧
      OInv x P n (fun j => Dn (due x j) ∨ due x j = cur) σ' ∧ σ'.vars "cur" = cur ∧
      σ.vars "kk" < σ'.vars "kk" ∧ σ'.vars "ib" = σ.vars "ib" ∧
      σ'.vars "hp" = σ.vars "hp" ∧ K + Psi n σ' ≤ Psi n σ + 7 := by
  classical
  have hne : jlist (due x) cur n ≠ [] := by
    simp only [occB, Bool.not_eq_false] at hocc
    intro hc; rw [hc] at hocc; simp at hocc
  have hjlB : hd1 (jlist (due x) cur n) ≤ n := hd1_le _ _ _
  set σ1 := σ.setVar "jp" (hd1 (jlist (due x) cur n)) with hσ1
  have hrun1 : Run B (.assign "jp" (.get "fj" (V "cur"))) σ σ1 3 :=
    (Run.assign (SweepBody.evalB_getE (SweepBody.evalB_var (by rw [hcur]; omega))
      (by omega) (by rw [hcur]; have := hsrc.lfj; have := hdLo cur hocc; omega)
      (by rw [hcur]; exact hsrc.fjv cur))).mono (by norm_num [Expr.size])
  have hI1 : EInvO x P n Lo M s Dn cur (σ.vars "kk") σ1 := by
    refine ⟨hsrc.setV (by decide) _, hbin.setV (by decide) (by decide) (by decide) _,
      by simpa [hσ1, Env.setVar] using hcur, n, le_refl n, by simp [hσ1, Env.setVar],
      (hoin.congrEm ?_).setV (by decide) _, by simp [hσ1, Env.setVar]⟩
    intro j hj
    simp only [EmAt]
    constructor
    · exact Or.inl
    · rintro (h | ⟨-, h2⟩)
      · exact h
      · omega
  have hdef : ∀ τ, EInvO x P n Lo M s Dn cur (σ.vars "kk") τ →
      ∃ v, (Cond.lt (lit 0) (V "jp")).evalB B τ = some v := by
    rintro τ ⟨-, -, -, r, hrn, hjp, -, -⟩
    exact ⟨_, evalB_lt0 (by omega) (by rw [hjp]; have := hd1_le (due x) cur r; omega)⟩
  have hstep : ∀ τ, EInvO x P n Lo M s Dn cur (σ.vars "kk") τ →
      (Cond.lt (lit 0) (V "jp")).evalB B τ = some true →
      ∃ τ' K, Run B emitStep τ τ' K ∧ EInvO x P n Lo M s Dn cur (σ.vars "kk") τ' ∧
        1 + (Cond.lt (lit 0) (V "jp")).size + K + Psi n τ' ≤ Psi n τ := by
    rintro τ ⟨hs, hb, hc, r, hrn, hjp, ho, hlen⟩ hcond
    have hjp0 : 0 < τ.vars "jp" := by
      rw [evalB_lt0 (by omega) (by rw [hjp]; have := hd1_le (due x) cur r; omega)] at hcond
      simpa using hcond
    obtain ⟨τ', hrun', hs', hb', ho', hc', hjp', hkk'⟩ :=
      emitStep_spec (B := B) (x := x) (P := P) (n := n) (Lo := Lo) (Dn := Dn) (s := s)
        (r := r) M hn cur hcB hrn hDn τ ⟨hs, hb, ho, hc, hjp, hjp0⟩
    have hlist : jlist (due x) cur r = (τ.vars "jp" - 1) :: jlist (due x) cur (τ.vars "jp" - 1) := by
      rw [hjp]; exact jlist_head (by omega)
    have hmem : (τ.vars "jp" - 1) ∈ jlist (due x) cur r := by rw [hlist]; exact List.mem_cons_self
    obtain ⟨har, -⟩ := (jlist_mem (due x) cur r _).mp hmem
    have hlen' : τ'.vars "kk" + (jlist (due x) cur (τ.vars "jp" - 1)).length
        = σ.vars "kk" + (jlist (due x) cur n).length := by
      rw [hkk', ← hlen, hlist]
      simp
      omega
    refine ⟨τ', 22, hrun', ⟨hs', hb', hc', τ.vars "jp" - 1, by omega, hjp', ho', hlen'⟩, ?_⟩
    have hkn : τ'.vars "kk" ≤ n := ho'.kkn
    simp only [Psi, Cond.size, Expr.size]
    omega
  obtain ⟨σ2, K0, hrun2, hI2, hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := .lt (lit 0) (V "jp")) (c := emitStep)
      (EInvO x P n Lo M s Dn cur (σ.vars "kk")) (Psi n) hdef hstep hI1
  obtain ⟨hs2, hb2, hc2, r2, hr2n, hjp2, ho2, hlen2⟩ := hI2
  have hjp2z : σ2.vars "jp" = 0 := by
    rw [evalB_lt0 (by omega) (by rw [hjp2]; have := hd1_le (due x) cur r2; omega)] at hfalse
    simpa using hfalse
  have hnil : jlist (due x) cur r2 = [] := by
    rw [← hd1_eq_zero_iff, ← hjp2, hjp2z]
  have hkk2 : σ2.vars "kk" = σ.vars "kk" + (jlist (due x) cur n).length := by
    rw [← hlen2, hnil]; simp
  have hpos : 0 < (jlist (due x) cur n).length := by
    cases hl : jlist (due x) cur n with
    | nil => exact absurd hl hne
    | cons _ _ => simp
  have hfr : Run B emitLoop σ σ2 (3 + K0) := Run.seq hrun1 hrun2
  refine ⟨σ2, 3 + K0, hfr, hs2, hb2, ho2.congrEm ?_, hc2, by omega,
    hfr.frame_var "ib" (by simp [emitLoop, emitStep, Com.wvars]),
    hfr.frame_var "hp" (by simp [emitLoop, emitStep, Com.wvars]), ?_⟩
  · intro j hj
    simp only [EmAt]
    constructor
    · rintro (h | ⟨h1, -⟩)
      · exact Or.inl h
      · exact Or.inr h1
    · rintro (h | h1)
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_⟩
        by_contra hcc
        have : j ∈ jlist (due x) cur r2 := (jlist_mem (due x) cur r2 j).mpr ⟨by omega, h1⟩
        rw [hnil] at this
        simp at this
  · have h1 : Psi n σ1 = Psi n σ := by simp [Psi, hσ1, Env.setVar]
    simp only [Cond.size, Expr.size] at hpay
    omega

/-! ### Walking one block -/

lemma chain_nodup {P M : ℕ} {occ : ℕ → Bool} (d : ℕ) : (chain P occ M d).Nodup :=
  (chain_sorted (P := P) (occ := occ) (M := M) d).imp (fun h => Nat.ne_of_lt h)

/-- The potential the middle loop runs on. -/
def Psi2 (n : ℕ) (σ : Env) : ℕ := 45 * (n - σ.vars "kk")

lemma evalB_eqlit {σ : Env} {y : String} {c : ℕ} (h : σ.vars y < B) (hc : c < B) :
    (Cond.eq (V y) (lit c)).evalB B σ = some (σ.vars y == c) := by
  simp [Cond.evalB, Expr.evalB, fit_self h, fit_self hc]

lemma BInvO.setCur {σ : Env} {s c : ℕ} (h : BInvO x P n M s σ)
    (hc : c ∈ chain P (occB x n) M s) (hle : σ.vars "cur" ≤ c) :
    BInvO x P n M s (σ.setVar "cur" c) := by
  have e0 : (σ.setVar "cur" c).vars "nc0" = σ.vars "nc0" := by simp [Env.setVar]
  have e1 : (σ.setVar "cur" c).vars "kk" = σ.vars "kk" := by simp [Env.setVar]
  have e2 : (σ.setVar "cur" c).vars "cur" = c := by simp [Env.setVar]
  have e3 : ∀ k, blkA (σ.setVar "cur" c) k = blkA σ k := fun k => blkA_congr fun t _ => rfl
  have e4 : nb (σ.setVar "cur" c) = nb σ := by rw [nb, nb, e0, e1, e3]
  exact { nc0le := by rw [e0]; exact h.nc0le
          first := by rw [e0, e1]; exact h.first
          curIn := by rw [e2]; exact hc
          prevle := by
            rw [e0, e1, e2]
            intro h1 h2
            exact le_trans (h.prevle h1 h2) hle
          sepcur := by rw [e1, e4]; simpa [e3] using h.sepcur }

/-- The state of the middle loop. -/
def WInv (x : List ℕ) (P n Lo M s : ℕ) (Dn0 : ℕ → Prop) (kk0 : ℕ) (σ : Env) : Prop :=
  Src x n P Lo σ ∧ kk0 ≤ σ.vars "kk" ∧
  ∃ pre : List ℕ,
    OInv x P n (fun j => Dn0 (due x j) ∨ due x j ∈ pre) σ ∧
    (pre ≠ [] → kk0 < σ.vars "kk") ∧
    ((σ.vars "ib" = 1 ∧ BInvO x P n M s σ ∧
        chain P (occB x n) M s = pre ++ chain P (occB x n) M (σ.vars "cur")) ∨
     (σ.vars "ib" = 0 ∧ chain P (occB x n) M s = pre))

theorem blockLoop_run (hM : ∀ e, occB x n e = true → e ≤ M) (hn : n + 2 < B)
    (hdB : ∀ d, occB x n d = true → d + 2 < B)
    (hdLo : ∀ d, occB x n d = true → d < Lo)
    (hDn0 : ∀ d, d ∈ chain P (occB x n) M s → ¬ Dn d)
    (hsocc : occB x n s = true)
    (σ : Env) (hsrc : Src x n P Lo σ) (hbin : BInvO x P n M s σ)
    (hoin : OInv x P n (fun j => Dn (due x j)) σ) (hcurs : σ.vars "cur" = s) :
    ∃ σ' K, Run B blockLoop σ σ' K ∧ Src x n P Lo σ' ∧
      OInv x P n (fun j => Dn (due x j) ∨ due x j ∈ chain P (occB x n) M s) σ' ∧
      σ.vars "kk" < σ'.vars "kk" ∧ K + Psi2 n σ' ≤ Psi2 n σ + 6 := by
  classical
  have hB1 : 1 < B := by omega
  set σ1 := σ.setVar "ib" 1 with hσ1
  have hrun1 : Run B (set "ib" (lit 1)) σ σ1 2 :=
    (Run.assign (SweepBody.evalB_lit (show (1 : ℕ) < B by omega))).mono
      (by norm_num [Expr.size])
  have hI1 : WInv x P n Lo M s Dn (σ.vars "kk") σ1 := by
    refine ⟨hsrc.setV (by decide) _, by simp [hσ1, Env.setVar], [], ?_, by simp, ?_⟩
    · exact (hoin.congrEm (fun j _ => by simp)).setV (by decide) _
    · exact Or.inl ⟨by simp [hσ1, Env.setVar],
        hbin.setV (by decide) (by decide) (by decide) _,
        by simp [hσ1, Env.setVar, hcurs]⟩
  have hib01 : ∀ τ : Env, WInv x P n Lo M s Dn (σ.vars "kk") τ → τ.vars "ib" ≤ 1 := by
    rintro τ ⟨-, -, pre, -, -, hd⟩
    rcases hd with ⟨h, -, -⟩ | ⟨h, -⟩ <;> omega
  have hdef : ∀ τ, WInv x P n Lo M s Dn (σ.vars "kk") τ →
      ∃ v, (Cond.eq (V "ib") (lit 1)).evalB B τ = some v :=
    fun τ hτ => ⟨_, evalB_eqlit (by have := hib01 τ hτ; omega) hB1⟩
  have hstep : ∀ τ, WInv x P n Lo M s Dn (σ.vars "kk") τ →
      (Cond.eq (V "ib") (lit 1)).evalB B τ = some true →
      ∃ τ' K, Run B walkBody τ τ' K ∧ WInv x P n Lo M s Dn (σ.vars "kk") τ' ∧
        1 + (Cond.eq (V "ib") (lit 1)).size + K + Psi2 n τ' ≤ Psi2 n τ := by
    rintro τ ⟨hs, hk0, pre, ho, hgrow, hd⟩ hcond
    have hib : τ.vars "ib" = 1 := by
      rw [evalB_eqlit (by have := hib01 τ ⟨hs, hk0, pre, ho, hgrow, hd⟩; omega) hB1] at hcond
      simpa using hcond
    obtain ⟨-, hb, hchain⟩ : τ.vars "ib" = 1 ∧ BInvO x P n M s τ ∧
        chain P (occB x n) M s = pre ++ chain P (occB x n) M (τ.vars "cur") := by
      rcases hd with h | ⟨h, -⟩
      · exact h
      · omega
    set cur := τ.vars "cur" with hcurdef
    have hcurmem : cur ∈ chain P (occB x n) M s := hb.curIn
    have hcurocc : occB x n cur = true := chain_occ s hsocc cur hcurmem
    have hcurpre : cur ∉ pre := by
      have hnd : (pre ++ chain P (occB x n) M cur).Nodup := by
        rw [← hchain]; exact chain_nodup s
      exact fun hc => (List.nodup_append.mp hnd).2.2 cur hc cur (mem_chain_self cur) rfl
    have hfresh : ¬ (Dn cur ∨ cur ∈ pre) := by
      rintro (h | h)
      · exact hDn0 cur hcurmem h
      · exact hcurpre h
    obtain ⟨τ1, K1, hrun1', hs1, hb1, ho1, hc1, hkk1, hib1, hhp1, hpay1⟩ :=
      emitLoop_run (B := B) (x := x) (P := P) (n := n) (Lo := Lo)
        (Dn := fun d => Dn d ∨ d ∈ pre) (s := s) M hn cur (by have := hdB cur hcurocc; omega)
        hfresh hcurocc hdLo τ hs hb ho rfl
    -- the test on `nx2`
    have hnx2 : (τ1.arrs "nx2").getD cur 0 = nxt P (occB x n) cur := by
      rw [hs1.nx2v cur hcurocc]
    have hnxB : nxt P (occB x n) cur < B := by
      by_cases h0 : nxt P (occB x n) cur = 0
      · omega
      · have := hdB _ (nxt_pos (P := P) (occ := occB x n) (d := cur) h0).1; omega
    have hcurB : cur < B := by have := hdB cur hcurocc; omega
    have hidx : cur < (τ1.arrs "nx2").length := by
      have := hs1.lnx2; have := hdLo cur hcurocc; omega
    have hcurle : cur ≤ M := hM cur hcurocc
    have hcEq : chain P (occB x n) M cur =
        if nxt P (occB x n) cur = 0 then [cur]
        else cur :: chain P (occB x n) M (nxt P (occB x n) cur) := chain_eq_of hM hcurle
    have hoNew : OInv x P n (fun j => Dn (due x j) ∨ due x j ∈ pre ++ [cur]) τ1 :=
      ho1.congrEm fun j _ => by simp [or_assoc]
    have hkkn : τ1.vars "kk" ≤ n := hoNew.kkn
    by_cases h0 : nxt P (occB x n) cur = 0
    · -- the block ends here
      refine ⟨τ1.setVar "ib" 0, K1 + 8, ?_, ?_, ?_⟩
      · refine (Run.seq hrun1' (Run.ite_true (K := 3) ?_ ?_)).mono
          (by norm_num [Cond.size, Expr.size])
        · have hev : (Expr.get "nx2" (V "cur")).evalB B τ1 = some (nxt P (occB x n) cur) :=
            SweepBody.evalB_getE (SweepBody.evalB_var (by rw [hc1]; omega)) hnxB
              (by rw [hc1]; exact hidx) (by rw [hc1]; exact hnx2)
          have hz : (lit 0).evalB B τ1 = some 0 :=
            SweepBody.evalB_lit (show (0 : ℕ) < B by omega)
          simp [Cond.evalB, hev, hz, h0]
        · exact (Run.assign (SweepBody.evalB_lit (show (0 : ℕ) < B by omega))).mono
            (by norm_num [Expr.size])
      · refine ⟨hs1.setV (by decide) _, ?_, pre ++ [cur], hoNew.setV (by decide) _, ?_,
          Or.inr ⟨by simp [Env.setVar], ?_⟩⟩
        · simp only [Env.setVar, String.reduceEq, ↓reduceIte]; omega
        · intro _; simp only [Env.setVar, String.reduceEq, ↓reduceIte]; omega
        · rw [hchain, hcEq, if_pos h0]
      · simp only [Psi2, Env.setVar, String.reduceEq, ↓reduceIte, Cond.size, Expr.size]
        simp only [Psi] at hpay1
        omega
    · -- step to the next deadline of the block
      refine ⟨τ1.setVar "cur" (nxt P (occB x n) cur), K1 + 8, ?_, ?_, ?_⟩
      · refine (Run.seq hrun1' (Run.ite_false (K := 3) ?_ ?_)).mono
          (by norm_num [Cond.size, Expr.size])
        · have hev : (Expr.get "nx2" (V "cur")).evalB B τ1 = some (nxt P (occB x n) cur) :=
            SweepBody.evalB_getE (SweepBody.evalB_var (by rw [hc1]; omega)) hnxB
              (by rw [hc1]; exact hidx) (by rw [hc1]; exact hnx2)
          have hz : (lit 0).evalB B τ1 = some 0 :=
            SweepBody.evalB_lit (show (0 : ℕ) < B by omega)
          simp [Cond.evalB, hev, hz, h0]
        · exact (Run.assign (SweepBody.evalB_getE
            (SweepBody.evalB_var (by rw [hc1]; omega)) hnxB
            (by rw [hc1]; exact hidx) (by rw [hc1]; exact hnx2))).mono
            (by norm_num [Expr.size])
      · have hchain' : chain P (occB x n) M s
            = (pre ++ [cur]) ++ chain P (occB x n) M (nxt P (occB x n) cur) := by
          rw [hchain, hcEq, if_neg h0]; simp
        have hmemn : nxt P (occB x n) cur ∈ chain P (occB x n) M s := by
          rw [hchain']
          exact List.mem_append_right _ (mem_chain_self _)
        refine ⟨hs1.setV (by decide) _, ?_, pre ++ [cur], hoNew.setV (by decide) _, ?_,
          Or.inl ⟨by simp [Env.setVar, hib1, hib], ?_, ?_⟩⟩
        · simp only [Env.setVar, String.reduceEq, ↓reduceIte]; omega
        · intro _; simp only [Env.setVar, String.reduceEq, ↓reduceIte]; omega
        · refine hb1.setCur hmemn ?_
          rw [hc1]
          exact le_of_lt (nxt_pos h0).2.1
        · rw [hchain']
          simp [Env.setVar]
      · simp only [Psi2, Env.setVar, String.reduceEq, ↓reduceIte, Cond.size, Expr.size]
        simp only [Psi] at hpay1
        omega
  obtain ⟨σ2, K0, hrun2, hI2, hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := .eq (V "ib") (lit 1)) (c := walkBody)
      (WInv x P n Lo M s Dn (σ.vars "kk")) (Psi2 n) hdef hstep hI1
  obtain ⟨hs2, hk2, pre2, ho2, hgrow2, hd2⟩ := hI2
  have hib2 : σ2.vars "ib" = 0 := by
    rw [evalB_eqlit (by have := hib01 σ2 ⟨hs2, hk2, pre2, ho2, hgrow2, hd2⟩; omega) hB1] at hfalse
    have : ¬ (σ2.vars "ib" = 1) := by simpa using hfalse
    have := hib01 σ2 ⟨hs2, hk2, pre2, ho2, hgrow2, hd2⟩
    omega
  have hpre2 : chain P (occB x n) M s = pre2 := by
    rcases hd2 with ⟨h, -, -⟩ | ⟨-, h⟩
    · omega
    · exact h
  have hne2 : pre2 ≠ [] := by
    rw [← hpre2]
    obtain ⟨t, ht⟩ := chain_head (P := P) (occ := occB x n) (M := M) s
    rw [ht]; simp
  refine ⟨σ2, 2 + K0, Run.seq hrun1 hrun2, hs2, ?_, hgrow2 hne2, ?_⟩
  · rw [hpre2]; exact ho2
  · have h1 : Psi2 n σ1 = Psi2 n σ := by simp [Psi2, hσ1, Env.setVar]
    simp only [Cond.size, Expr.size] at hpay
    omega

/-! ### Opening the blocks -/

lemma hd1_eq_succ {f : ℕ → ℕ} {d N h : ℕ} (he : hd1 (jlist f d N) = h + 1) :
    f h = d ∧ h < N := by
  rcases hl : jlist f d N with _ | ⟨b, l⟩
  · rw [hl] at he; simp [hd1] at he
  · rw [hl] at he
    simp only [hd1] at he
    have hb : b = h := by omega
    subst hb
    exact ⟨((jlist_mem f d N b).mp (by rw [hl]; exact List.mem_cons_self)).2,
      ((jlist_mem f d N b).mp (by rw [hl]; exact List.mem_cons_self)).1⟩

/-- A block start whose closing job has already been passed. -/
def OpenedAt (x : List ℕ) (P n hp t : ℕ) : Prop :=
  isStart P (occB x n) t = true ∧ 0 < hd1 (jlist (due x) t n) ∧
    hd1 (jlist (due x) t n) ≤ hp

/-- The deadlines already written out. -/
def DnAt (x : List ℕ) (P n M hp d : ℕ) : Prop :=
  ∃ t, OpenedAt x P n hp t ∧ d ∈ chain P (occB x n) M t

lemma DnAt_succ (hp : ℕ) (d : ℕ) :
    DnAt x P n M (hp + 1) d ↔
      (DnAt x P n M hp d ∨
        (isStart P (occB x n) (due x hp) = true ∧
          hd1 (jlist (due x) (due x hp) n) = hp + 1 ∧
          d ∈ chain P (occB x n) M (due x hp))) := by
  constructor
  · rintro ⟨t, ⟨h1, h2, h3⟩, h4⟩
    rcases Nat.lt_or_ge (hd1 (jlist (due x) t n)) (hp + 1) with hlt | hge
    · exact Or.inl ⟨t, ⟨h1, h2, by omega⟩, h4⟩
    · have he : hd1 (jlist (due x) t n) = hp + 1 := by omega
      obtain ⟨hdt, -⟩ := hd1_eq_succ he
      subst hdt
      exact Or.inr ⟨h1, he, h4⟩
  · rintro (⟨t, ⟨h1, h2, h3⟩, h4⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨t, ⟨h1, h2, by omega⟩, h4⟩
    · exact ⟨due x hp, ⟨h1, by omega, by omega⟩, h3⟩

/-- The state of the outer loop. -/
def OuterInv (x : List ℕ) (P n Lo M : ℕ) (σ : Env) : Prop :=
  Src x n P Lo σ ∧ σ.vars "hp" ≤ n ∧
    OInv x P n (fun j => DnAt x P n M (σ.vars "hp") (due x j)) σ

lemma isStart_occ {P : ℕ} {occ : ℕ → Bool} {d : ℕ} (h : isStart P occ d = true) :
    occ d = true := (Bool.and_eq_true _ _ |>.mp h).1

lemma DnAt_occ {hp d : ℕ} (h : DnAt x P n M hp d) : occB x n d = true := by
  obtain ⟨t, ⟨h1, -, -⟩, h4⟩ := h
  exact chain_occ t (isStart_occ h1) d h4

lemma sep_new_block (hM : ∀ e, occB x n e = true → e ≤ M) (hocc0 : occB x n 0 = false)
    {hp dd : ℕ} (hst : isStart P (occB x n) dd = true)
    (hnew : ¬ OpenedAt x P n hp dd) {d e : ℕ} (hd : d ∈ chain P (occB x n) M dd)
    (he : DnAt x P n M hp e) : e + P ≤ d ∨ d + P ≤ e := by
  obtain ⟨t, hop, hmem⟩ := he
  have hene : e ∉ chain P (occB x n) M dd := by
    intro hc
    exact hnew (by rw [start_unique hocc0 hop.1 hst hmem hc] at hop; exact hop)
  rcases chain_sep hM hocc0 hst hd (DnAt_occ ⟨t, hop, hmem⟩) hene with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem openStep_run (hM : ∀ e, occB x n e = true → e ≤ M)
    (hocc0 : occB x n 0 = false) (hn : n + 2 < B)
    (hdB : ∀ d, occB x n d = true → d + 2 < B)
    (hdLo : ∀ d, occB x n d = true → d < Lo)
    (hjc : jobCount x = n) (hxlen : 2 + n + n ≤ x.length) (hxB : x.length + 2 < B)
    (hP : 0 < P) (σ : Env) (hsrc : Src x n P Lo σ)
    (hoin : OInv x P n (fun j => DnAt x P n M (σ.vars "hp") (due x j)) σ)
    (hhp : σ.vars "hp" < n) :
    ∃ σ' K, Run B openStep σ σ' K ∧ Src x n P Lo σ' ∧
      σ'.vars "hp" = σ.vars "hp" ∧
      OInv x P n (fun j => DnAt x P n M (σ.vars "hp" + 1) (due x j)) σ' ∧
      K + Psi2 n σ' ≤ Psi2 n σ + 29 := by
  classical
  set hp := σ.vars "hp" with hpdef
  set dd := due x hp with hdddef
  have hnv : σ.vars "n" = n := hsrc.varn
  have haL : (σ.arrs "a").length = x.length := by rw [hsrc.arrA]
  have hddocc : occB x n dd = true := by
    have hm : hp ∈ jlist (due x) dd n := (jlist_mem (due x) dd n hp).mpr ⟨hhp, rfl⟩
    have hne : jlist (due x) dd n ≠ [] := by intro hc; rw [hc] at hm; simp at hm
    simp [occB, List.isEmpty_iff, hne]
  have hddB : dd + 2 < B := hdB dd hddocc
  have hddLo : dd < Lo := hdLo dd hddocc
  have hread : (σ.arrs "a").getD (2 + σ.vars "n" + hp) 0 = dd := by
    rw [hsrc.arrA, hsrc.varn, hdddef, due, hjc]
  have hevdd : (Expr.get "a" (add (add (lit 2) (V "n")) (V "hp"))).evalB B σ = some dd := by
    refine SweepBody.evalB_getE (SweepBody.evalB_add (SweepBody.evalB_add
      (SweepBody.evalB_lit (by omega)) (SweepBody.evalB_var (by rw [hnv]; omega))
      (by rw [hnv]; omega)) (SweepBody.evalB_var (by omega))
      (by rw [hnv]; omega)) (by omega) (by rw [hnv, haL]; omega) hread
  set σ1 := σ.setVar "dd" dd with hσ1
  have hrun1 : Run B (.assign "dd" (.get "a" (add (add (lit 2) (V "n")) (V "hp")))) σ σ1 7 :=
    (Run.assign hevdd).mono (by norm_num [Expr.size])
  have hsrc1 : Src x n P Lo σ1 := hsrc.setV (by decide) _
  have hoin1 : OInv x P n (fun j => DnAt x P n M hp (due x j)) σ1 :=
    hoin.setV (by decide) _
  have hdd1 : σ1.vars "dd" = dd := by simp [hσ1, Env.setVar]
  have hhp1 : σ1.vars "hp" = hp := by simp [hσ1, Env.setVar, hpdef]
  have hkk1 : σ1.vars "kk" = σ.vars "kk" := by simp [hσ1, Env.setVar]
  -- the two tests
  have hstv : (σ1.arrs "st").getD dd 0 = (if isStart P (occB x n) dd then 1 else 0) :=
    hsrc1.stv dd hddocc
  have hfjv : (σ1.arrs "fj").getD dd 0 = hd1 (jlist (due x) dd n) := hsrc1.fjv dd
  have hevst : (Expr.get "st" (V "dd")).evalB B σ1
      = some (if isStart P (occB x n) dd then 1 else 0) :=
    SweepBody.evalB_getE (SweepBody.evalB_var (by rw [hdd1]; omega))
      (by split <;> omega) (by rw [hdd1]; have := hsrc1.lst; omega) (by rw [hdd1]; exact hstv)
  have hevfj : (Expr.get "fj" (V "dd")).evalB B σ1 = some (hd1 (jlist (due x) dd n)) :=
    SweepBody.evalB_getE (SweepBody.evalB_var (by rw [hdd1]; omega))
      (by have := hd1_le (due x) dd n; omega)
      (by rw [hdd1]; have := hsrc1.lfj; omega) (by rw [hdd1]; exact hfjv)
  have hevhp1 : (add (V "hp") (lit 1)).evalB B σ1 = some (hp + 1) := by
    have := SweepBody.evalB_add (B := B) (σ := σ1)
      (SweepBody.evalB_var (y := "hp") (by rw [hhp1]; omega))
      (SweepBody.evalB_lit (show (1 : ℕ) < B by omega)) (by rw [hhp1]; omega)
    rwa [hhp1] at this
  have hnoop : OInv x P n (fun j => DnAt x P n M hp (due x j)) σ1 →
      ¬ (isStart P (occB x n) dd = true ∧ hd1 (jlist (due x) dd n) = hp + 1) →
      OInv x P n (fun j => DnAt x P n M (hp + 1) (due x j)) σ1 := by
    intro h hcon
    refine h.congrEm fun j hj => ?_
    rw [DnAt_succ]
    constructor
    · exact Or.inl
    · rintro (h1 | ⟨h1, h2, h3⟩)
      · exact h1
      · exact absurd ⟨h1, h2⟩ hcon
  by_cases hcase : isStart P (occB x n) dd = true ∧ hd1 (jlist (due x) dd n) = hp + 1
  · obtain ⟨hst, hfj⟩ := hcase
    -- open the block at dd
    set σ2 := (σ1.setVar "cur" dd).setVar "nc0" 1 with hσ2
    have hrunA : Run B (.assign "cur" (V "dd")) σ1 (σ1.setVar "cur" dd) 2 :=
      (Run.assign (by rw [← hdd1]; exact SweepBody.evalB_var (by rw [hdd1]; omega))).mono
        (by norm_num [Expr.size])
    have hrunB : Run B (set "nc0" (lit 1)) (σ1.setVar "cur" dd) σ2 2 :=
      (Run.assign (SweepBody.evalB_lit (show (1 : ℕ) < B by omega))).mono
        (by norm_num [Expr.size])
    have hnew : ¬ OpenedAt x P n hp dd := by
      rintro ⟨-, -, h3⟩; omega
    have hsep : ∀ e, DnAt x P n M hp e → ∀ d, d ∈ chain P (occB x n) M dd →
        e + P ≤ d ∨ d + P ≤ e := fun e he d hd => sep_new_block hM hocc0 hst hnew hd he
    have hsrc2 : Src x n P Lo σ2 := (hsrc1.setV (by decide) _).setV (by decide) _
    have hoin2 : OInv x P n (fun j => DnAt x P n M hp (due x j)) σ2 :=
      (hoin1.setV (by decide) _).setV (by decide) _
    have hkk2 : σ2.vars "kk" = σ.vars "kk" := by simp [hσ2, hσ1, Env.setVar]
    have hcur2 : σ2.vars "cur" = dd := by simp [hσ2, Env.setVar]
    have hnc02 : σ2.vars "nc0" = 1 := by simp [hσ2, Env.setVar]
    have hbin2 : BInvO x P n M dd σ2 := by
      refine ⟨by rw [hnc02], by rw [hnc02]; intro _; rfl, by rw [hcur2]; exact mem_chain_self dd,
        by intro _ h; rw [hnc02] at h; omega, ?_⟩
      intro a ha _ d hd
      have hDd : DnAt x P n M hp ((σ2.arrs "dl").getD a 0) := by
        have hj := (hoin2.cov ((σ2.arrs "ord").getD a 0) (hoin2.lt a ha)).mp ⟨a, ha, rfl⟩
        rwa [← hoin2.dle a ha] at hj
      exact hsep _ hDd d hd
    obtain ⟨σ3, Kb, hrun3, hsrc3, hoin3, hkk3, hpay3⟩ :=
      blockLoop_run (B := B) (x := x) (P := P) (n := n) (Lo := Lo)
        (Dn := DnAt x P n M hp) (s := dd) hM hn hdB hdLo
        (fun d hd hDd => by rcases hsep d hDd d hd with h | h <;> omega)
        hddocc σ2 hsrc2 hbin2 hoin2 hcur2
    refine ⟨σ3, 7 + (1 + 4 + (1 + 6 + (2 + (2 + Kb)))), ?_, hsrc3, ?_, ?_, ?_⟩
    · refine Run.seq hrun1 (Run.ite_true ?_ (Run.ite_true ?_
        (Run.seq hrunA (Run.seq hrunB hrun3))))
      · rw [Cond.evalB, hevst, hst]
        simp [SweepBody.evalB_lit (show (1 : ℕ) < B by omega)]
      · rw [Cond.evalB, hevfj, hevhp1, hfj]
        simp
    · rw [← hhp1]
      exact (hrun3.frame_var "hp" (by simp [blockLoop, walkBody, emitLoop, emitStep, Com.wvars])).trans
        (by simp [hσ2, hσ1, Env.setVar])
    · refine hoin3.congrEm fun j hj => ?_
      rw [DnAt_succ]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨hst, hfj, h⟩
      · rintro (h | ⟨-, -, h3⟩)
        · exact Or.inl h
        · exact Or.inr h3
    · simp only [Psi2] at hpay3 ⊢
      rw [hkk2] at hpay3
      omega
  · -- nothing opens here
    by_cases hst : isStart P (occB x n) dd = true
    · refine ⟨σ1, 7 + (1 + 4 + (1 + 6 + 1)), ?_, hsrc1, hhp1, hnoop hoin1 hcase, ?_⟩
      · refine Run.seq hrun1 (Run.ite_true ?_ (Run.ite_false ?_ Run.skip))
        · rw [Cond.evalB, hevst, hst]
          simp [SweepBody.evalB_lit (show (1 : ℕ) < B by omega)]
        · rw [Cond.evalB, hevfj, hevhp1]
          have : hd1 (jlist (due x) dd n) ≠ hp + 1 := fun hc => hcase ⟨hst, hc⟩
          simp [this]
      · simp only [Psi2, hσ1, Env.setVar, String.reduceEq, ↓reduceIte]
        omega
    · refine ⟨σ1, 7 + (1 + 4 + 1), ?_, hsrc1, hhp1, hnoop hoin1 hcase, ?_⟩
      · refine Run.seq hrun1 (Run.ite_false ?_ Run.skip)
        rw [Cond.evalB, hevst, if_neg hst]
        simp [SweepBody.evalB_lit (show (1 : ℕ) < B by omega)]
      · simp only [Psi2, hσ1, Env.setVar, String.reduceEq, ↓reduceIte]
        omega

/-! ### The pass -/

/-- The potential the outer loop runs on. -/
def PhiO (n : ℕ) (σ : Env) : ℕ := Psi2 n σ + 37 * (n - σ.vars "hp")

theorem orderLoop_run (hM : ∀ e, occB x n e = true → e ≤ M)
    (hocc0 : occB x n 0 = false) (hn : n + 2 < B)
    (hdB : ∀ d, occB x n d = true → d + 2 < B)
    (hdLo : ∀ d, occB x n d = true → d < Lo)
    (hjc : jobCount x = n) (hxlen : 2 + n + n ≤ x.length) (hxB : x.length + 2 < B)
    (hP : 0 < P) (σ : Env) (hsrc : Src x n P Lo σ) :
    ∃ σ' K, Run B orderLoop σ σ' K ∧ Src x n P Lo σ' ∧ σ'.vars "hp" = n ∧
      OInv x P n (fun j => DnAt x P n M n (due x j)) σ' ∧ K ≤ 82 * n + 8 := by
  classical
  set σ1 := (σ.setVar "kk" 0).setVar "hp" 0 with hσ1
  have hrunA : Run B (set "kk" (lit 0)) σ (σ.setVar "kk" 0) 2 :=
    (Run.assign (SweepBody.evalB_lit (show (0 : ℕ) < B by omega))).mono
      (by norm_num [Expr.size])
  have hrunB : Run B (set "hp" (lit 0)) (σ.setVar "kk" 0) σ1 2 :=
    (Run.assign (SweepBody.evalB_lit (show (0 : ℕ) < B by omega))).mono
      (by norm_num [Expr.size])
  have hkk1 : σ1.vars "kk" = 0 := by simp [hσ1, Env.setVar]
  have hhp1 : σ1.vars "hp" = 0 := by simp [hσ1, Env.setVar]
  have hsrc1 : Src x n P Lo σ1 := (hsrc.setV (by decide) _).setV (by decide) _
  have hI1 : OuterInv x P n Lo M σ1 := by
    refine ⟨hsrc1, by rw [hhp1]; omega, ?_⟩
    refine ⟨by rw [hkk1]; omega, by rw [hkk1]; intro k hk; omega,
      by rw [hkk1]; intro k hk; omega, by rw [hkk1]; intro k hk; omega, ?_,
      by rw [hkk1]; intro a b ha; omega, by rw [hkk1]; intro h; omega,
      by rw [hkk1]; intro k _ hk; omega, by rw [hkk1]; intro a b ha; omega⟩
    intro j hj
    rw [hkk1, hhp1]
    constructor
    · rintro ⟨k, hk, -⟩; omega
    · rintro ⟨t, ⟨-, h2, h3⟩, -⟩; omega
  have hdef : ∀ τ, OuterInv x P n Lo M τ →
      ∃ v, (Cond.lt (V "hp") (V "n")).evalB B τ = some v := by
    rintro τ ⟨hs, hhp, -⟩
    exact evalB_condLt_vars (show τ.vars "hp" < B by omega)
      (show τ.vars "n" < B by rw [hs.varn]; omega)
  have hstep : ∀ τ, OuterInv x P n Lo M τ →
      (Cond.lt (V "hp") (V "n")).evalB B τ = some true →
      ∃ τ' K, Run B orderBody τ τ' K ∧ OuterInv x P n Lo M τ' ∧
        1 + (Cond.lt (V "hp") (V "n")).size + K + PhiO n τ' ≤ PhiO n τ := by
    rintro τ ⟨hs, hhple, ho⟩ hcond
    have hhplt : τ.vars "hp" < n := by
      have := lt_of_condLt_true hcond
      rw [hs.varn] at this
      exact this
    obtain ⟨τ1, K1, hrunb, hs1, hhpb, ho1, hpay1⟩ :=
      openStep_run (B := B) (x := x) (P := P) (n := n) (Lo := Lo) (M := M)
        hM hocc0 hn hdB hdLo hjc hxlen hxB hP τ hs ho hhplt
    have hevb : (add (V "hp") (lit 1)).evalB B τ1 = some (τ.vars "hp" + 1) := by
      have h := SweepBody.evalB_add (B := B) (σ := τ1)
        (SweepBody.evalB_var (y := "hp") (by rw [hhpb]; omega))
        (SweepBody.evalB_lit (show (1 : ℕ) < B by omega)) (by rw [hhpb]; omega)
      rwa [hhpb] at h
    have hhpS : (τ1.setVar "hp" (τ.vars "hp" + 1)).vars "hp" = τ.vars "hp" + 1 := by
      simp [Env.setVar]
    refine ⟨τ1.setVar "hp" (τ.vars "hp" + 1), K1 + 4,
      Run.seq hrunb ((Run.assign hevb).mono (by norm_num [Expr.size])), ?_, ?_⟩
    · refine ⟨hs1.setV (by decide) _, by rw [hhpS]; omega, ?_⟩
      rw [hhpS]
      exact ho1.setV (by decide) _
    · have hkke : (τ1.setVar "hp" (τ.vars "hp" + 1)).vars "kk" = τ1.vars "kk" := by
        simp [Env.setVar]
      simp only [PhiO, Psi2, Cond.size, Expr.size, Env.setVar, String.reduceEq, ↓reduceIte]
      simp only [Psi2] at hpay1
      omega
  obtain ⟨σ2, K0, hrun2, hI2, hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := .lt (V "hp") (V "n")) (c := orderBody)
      (OuterInv x P n Lo M) (PhiO n) hdef hstep hI1
  obtain ⟨hs2, hhp2, ho2⟩ := hI2
  have hhpn : σ2.vars "hp" = n := by
    have h1 := le_of_condLt_false hfalse
    rw [hs2.varn] at h1
    omega
  rw [hhpn] at ho2
  refine ⟨σ2, 2 + (2 + K0), Run.seq hrunA (Run.seq hrunB hrun2), hs2, hhpn, ho2, ?_⟩
  have hPhi1 : PhiO n σ1 = 82 * n := by
    simp only [PhiO, Psi2, hkk1, hhp1]
    omega
  simp only [Cond.size, Expr.size] at hpay
  omega

/-! ### The contract the sweep asks for -/

lemma nc_conv {v : ℕ} (h : v ≤ 1) : v = if decide (v = 1) then 1 else 0 := by
  interval_cases v <;> simp

open Lax470956Proofs.SweepLoop in
theorem order_final {I : Instance} {σ : Env}
    (hjobs : n = I.jobs) (hnpos : 0 < n)
    (hdue : ∀ j : Fin I.jobs, due x j.val = I.d j)
    (hpP : ∀ j : Fin I.jobs, I.p j ≤ P)
    (hM : ∀ e, occB x n e = true → e ≤ M) (hocc0 : occB x n 0 = false)
    (hoin : OInv x P n (fun j => DnAt x P n M n (due x j)) σ) :
    σ.vars "kk" = n ∧
    ∃ (ordF : ℕ → Fin I.jobs) (dlF : ℕ → ℕ) (ncF : ℕ → Bool),
      Order I P n ordF dlF ncF ∧
      (∀ k, k < n → (σ.arrs "ord").getD k 0 = (ordF k).val) ∧
      (∀ k, k < n → (σ.arrs "dl").getD k 0 = dlF k) ∧
      (∀ k, k < n → (σ.arrs "nc").getD k 0 = if ncF k then 1 else 0) := by
  classical
  have hjpos : 0 < I.jobs := by omega
  -- every job's deadline lies on an opened walk
  have hcover : ∀ j, j < n → DnAt x P n M n (due x j) := by
    intro j hj
    have hocc : occB x n (due x j) = true := by
      have hm : j ∈ jlist (due x) (due x j) n := (jlist_mem (due x) (due x j) n j).mpr ⟨hj, rfl⟩
      have hne : jlist (due x) (due x j) n ≠ [] := by intro hc; rw [hc] at hm; simp at hm
      simp [occB, List.isEmpty_iff, hne]
    obtain ⟨s, hs, hmem⟩ := exists_start (P := P) (M := M) hM hocc0 (due x j) hocc
    have hsocc : occB x n s = true := isStart_occ hs
    have hsne : jlist (due x) s n ≠ [] := by
      simp only [occB, List.isEmpty_iff] at hsocc
      simpa using hsocc
    have hpos : 0 < hd1 (jlist (due x) s n) := by
      rcases hl : jlist (due x) s n with _ | ⟨b, l⟩
      · exact absurd hl hsne
      · simp [hd1]
    exact ⟨s, ⟨hs, hpos, hd1_le _ _ _⟩, hmem⟩
  -- the pass wrote out every job
  have hsurj : ∀ j, j < n → ∃ k, k < σ.vars "kk" ∧ (σ.arrs "ord").getD k 0 = j :=
    fun j hj => (hoin.cov j hj).mpr (hcover j hj)
  have hkkn : σ.vars "kk" = n := by
    refine le_antisymm hoin.kkn ?_
    have hsub : Finset.range n ⊆ (Finset.range (σ.vars "kk")).image
        (fun k => (σ.arrs "ord").getD k 0) := by
      intro j hj
      obtain ⟨k, hk, hkj⟩ := hsurj j (Finset.mem_range.mp hj)
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, hkj⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact le_trans this (le_trans (Finset.card_image_le) (by rw [Finset.card_range]))
  refine ⟨hkkn, fun k => if h : (σ.arrs "ord").getD k 0 < I.jobs then ⟨_, h⟩ else ⟨0, hjpos⟩,
    fun k => (σ.arrs "dl").getD k 0, fun k => decide ((σ.arrs "nc").getD k 0 = 1), ?_, ?_, ?_, ?_⟩
  · refine ⟨fun j => hpP j, hjobs, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b ha hb hab
      have ha' : (σ.arrs "ord").getD a 0 < I.jobs := by
        have := hoin.lt a (by omega); omega
      have hb' : (σ.arrs "ord").getD b 0 < I.jobs := by
        have := hoin.lt b (by omega); omega
      rw [dif_pos ha', dif_pos hb'] at hab
      exact hoin.inj a b (by omega) (by omega) (congrArg Fin.val hab)
    · intro k hk
      have hk' : (σ.arrs "ord").getD k 0 < I.jobs := by have := hoin.lt k (by omega); omega
      rw [dif_pos hk', ← hdue ⟨_, hk'⟩]
      exact hoin.dle k (by omega)
    · intro k hk hnc hk0
      have h01 := hoin.nc01 k (by omega)
      have hne1 : (σ.arrs "nc").getD k 0 ≠ 1 := by simpa using hnc
      exact hoin.mono k hk0 (by omega) (by omega)
    · exact decide_eq_true (hoin.cut0 (by omega))
    · intro k hk hnc a hak b hkb hbn
      -- the blocks are P apart
      have hka : blkA σ a < blkA σ k := by
        have h1 : blkA σ a ≤ blkA σ (k - 1) := blkA_mono σ (by omega)
        have h2 : blkA σ (k - 1 + 1) = blkA σ (k - 1) + (σ.arrs "nc").getD (k - 1 + 1) 0 :=
          blkA_succ σ (k - 1)
        rw [show k - 1 + 1 = k from by omega] at h2
        have h3 : (σ.arrs "nc").getD k 0 = 1 := by simpa using hnc
        omega
      have hkb' : blkA σ k ≤ blkA σ b := blkA_mono σ hkb
      have hsep := hoin.sep a b (by omega) (by omega) (by omega)
      have hda : (σ.arrs "dl").getD a 0 = I.d (if h : (σ.arrs "ord").getD a 0 < I.jobs then
          ⟨_, h⟩ else ⟨0, hjpos⟩) := by
        have ha' : (σ.arrs "ord").getD a 0 < I.jobs := by
          have := hoin.lt a (by omega); omega
        rw [dif_pos ha', ← hdue ⟨_, ha'⟩]
        exact hoin.dle a (by omega)
      have hdb : (σ.arrs "dl").getD b 0 = I.d (if h : (σ.arrs "ord").getD b 0 < I.jobs then
          ⟨_, h⟩ else ⟨0, hjpos⟩) := by
        have hb' : (σ.arrs "ord").getD b 0 < I.jobs := by
          have := hoin.lt b (by omega); omega
        rw [dif_pos hb', ← hdue ⟨_, hb'⟩]
        exact hoin.dle b (by omega)
      rintro ⟨h1, h2⟩
      simp only [Instance.start] at h1 h2
      rw [hda, hdb] at hsep
      have hpa := hpP (if h : (σ.arrs "ord").getD a 0 < I.jobs then ⟨_, h⟩ else ⟨0, hjpos⟩)
      have hpb := hpP (if h : (σ.arrs "ord").getD b 0 < I.jobs then ⟨_, h⟩ else ⟨0, hjpos⟩)
      omega
  · intro k hk
    have hk' : (σ.arrs "ord").getD k 0 < I.jobs := by have := hoin.lt k (by omega); omega
    simp only [dif_pos hk']
  · intro k hk; rfl
  · intro k hk
    have h01 := hoin.nc01 k (by omega)
    exact nc_conv h01

end Lax470956Proofs.SweepOrder
