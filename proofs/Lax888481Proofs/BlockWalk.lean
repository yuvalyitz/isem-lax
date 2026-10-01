import Mathlib.Tactic

/-!
Blocks of deadlines.

Jobs whose deadlines are `P` apart or more never overlap, so the occupied deadlines split
into blocks — maximal runs in which consecutive occupied points are less than `P` apart —
and the blocks are solved independently. This file walks a block: from its first point,
`nxt` steps to the next occupied point within `P`, and the walk enumerates the block in
increasing order. What the sweep needs of it is here: the walk is sorted, every occupied
point lies on exactly one walk, and a point off a walk is `P` away from every point on
it.
-/

namespace Lax888481Proofs.BlockWalk

variable (occ : ℕ → Bool)

/-- Scan `k` cells above `d` for an occupied one. -/
def nxtAux (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if occ (d + 1) then d + 1 else nxtAux (d + 1) k

variable {occ}

lemma nxtAux_spec (d k : ℕ) :
    (nxtAux occ d k = 0 ∧ ∀ e, d < e → e ≤ d + k → occ e = false) ∨
    (occ (nxtAux occ d k) = true ∧ d < nxtAux occ d k ∧ nxtAux occ d k ≤ d + k ∧
      ∀ e, d < e → e < nxtAux occ d k → occ e = false) := by
  induction k generalizing d with
  | zero => exact Or.inl ⟨rfl, fun e h1 h2 => by omega⟩
  | succ k ih =>
      by_cases h : occ (d + 1) = true
      · have he : nxtAux occ d (k + 1) = d + 1 := by simp [nxtAux, h]
        refine Or.inr ⟨by rw [he]; exact h, by omega, by omega, fun e h1 h2 => ?_⟩
        rw [he] at h2; omega
      · simp only [Bool.not_eq_true] at h
        have hstep : nxtAux occ d (k + 1) = nxtAux occ (d + 1) k := by simp [nxtAux, h]
        rcases ih (d + 1) with ⟨h0, hall⟩ | ⟨ho, h1, h2, h3⟩
        · refine Or.inl ⟨by rw [hstep, h0], fun e he1 he2 => ?_⟩
          rcases Nat.eq_or_lt_of_le he1 with he | he
          · rw [← he]; exact h
          · exact hall e (by omega) (by omega)
        · refine Or.inr ⟨by rw [hstep]; exact ho, by rw [hstep]; omega, by rw [hstep]; omega,
            fun e he1 he2 => ?_⟩
          rw [hstep] at he2
          rcases Nat.eq_or_lt_of_le he1 with he | he
          · rw [← he]; exact h
          · exact h3 e (by omega) he2

/-- The next occupied point strictly within `P` above `d`, or `0` if there is none. -/
def nxt (P : ℕ) (occ : ℕ → Bool) (d : ℕ) : ℕ := nxtAux occ d (P - 1)

/-- `d` starts a block: it is occupied, and nothing strictly within `P` below it is. -/
def isStart (P : ℕ) (occ : ℕ → Bool) (d : ℕ) : Bool :=
  occ d && ((List.range (P - 1)).all fun e => !occ (d - 1 - e))

variable {P : ℕ} {occ : ℕ → Bool} {d : ℕ}

lemma nxt_zero (h : nxt P occ d = 0) : ∀ e, d < e → e < d + P → occ e = false := by
  intro e h1 h2
  rcases nxtAux_spec (occ := occ) d (P - 1) with ⟨-, hall⟩ | ⟨-, hlt, -, -⟩
  · exact hall e h1 (by omega)
  · rw [nxt] at h; omega

lemma nxt_pos (h : nxt P occ d ≠ 0) :
    occ (nxt P occ d) = true ∧ d < nxt P occ d ∧ nxt P occ d < d + P ∧
      ∀ e, d < e → e < nxt P occ d → occ e = false := by
  rcases nxtAux_spec (occ := occ) d (P - 1) with ⟨h0, -⟩ | ⟨ho, h1, h2, h3⟩
  · exact absurd (by rw [nxt, h0]) h
  · exact ⟨ho, h1, by rw [nxt]; omega, fun e he1 he2 => h3 e he1 (by rw [nxt] at he2; exact he2)⟩

lemma isStart_iff (hocc0 : occ 0 = false) (d : ℕ) :
    isStart P occ d = true ↔ occ d = true ∧ ∀ e, e < d → d < e + P → occ e = false := by
  simp only [isStart, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun e he1 he2 => ?_⟩
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exact hocc0
    · have := h2 (d - 1 - e) (by omega)
      rwa [show d - 1 - (d - 1 - e) = e by omega] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun e he => ?_⟩
    rcases Nat.eq_zero_or_pos (d - 1 - e) with hz | hpos
    · rw [hz]; exact hocc0
    · exact h2 (d - 1 - e) (by omega) (by omega)

/-! ### The Walk -/

variable (P : ℕ) (occ : ℕ → Bool) (M : ℕ)

/-- The walk from `d`: the occupied points of `d`'s block, from `d` upward. -/
def chain : ℕ → List ℕ
  | d => if h : nxt P occ d = 0 ∨ M ≤ d then [d] else
      have : M - nxt P occ d < M - d := by
        have hp := nxt_pos (P := P) (occ := occ) (d := d) (by tauto)
        have : ¬ M ≤ d := by tauto
        omega
      d :: chain (nxt P occ d)
  termination_by d => M - d

variable {P occ M}

lemma chain_cons {d : ℕ} (h : ¬ (nxt P occ d = 0 ∨ M ≤ d)) :
    chain P occ M d = d :: chain P occ M (nxt P occ d) := by
  rw [chain, dif_neg h]

lemma chain_single {d : ℕ} (h : nxt P occ d = 0 ∨ M ≤ d) : chain P occ M d = [d] := by
  rw [chain, dif_pos h]

lemma chain_eq_of (hM : ∀ e, occ e = true → e ≤ M) {d : ℕ} (hd : d ≤ M) :
    chain P occ M d = if nxt P occ d = 0 then [d] else d :: chain P occ M (nxt P occ d) := by
  by_cases h : nxt P occ d = 0
  · rw [if_pos h, chain_single (Or.inl h)]
  · have hp := nxt_pos (P := P) (occ := occ) (d := d) h
    have hle := hM _ hp.1
    rw [if_neg h, chain_cons (by omega)]

lemma chain_head (d : ℕ) : ∃ t, chain P occ M d = d :: t := by
  by_cases h : nxt P occ d = 0 ∨ M ≤ d
  · exact ⟨[], chain_single h⟩
  · exact ⟨_, chain_cons h⟩

lemma mem_chain_self (d : ℕ) : d ∈ chain P occ M d := by
  obtain ⟨t, ht⟩ := chain_head (P := P) (occ := occ) (M := M) d
  rw [ht]; exact List.mem_cons_self

/-- The walk increases. -/
lemma chain_lb : ∀ (d : ℕ), ∀ x ∈ chain P occ M d, d ≤ x := by
  intro d
  induction d using chain.induct P occ M with
  | case1 e d h => intro x hx; rw [chain_single h] at hx; simp at hx; omega
  | case2 e d h hmm ih =>
      intro x hx
      rw [chain_cons h, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_refl _
      · have hp := nxt_pos (P := P) (occ := occ) (d := e) (by tauto)
        exact le_trans (by omega) (ih x hx)

lemma chain_sorted : ∀ (d : ℕ), (chain P occ M d).Pairwise (· < ·) := by
  intro d
  induction d using chain.induct P occ M with
  | case1 e d h => rw [chain_single h]; simp
  | case2 e d h hmm ih =>
      rw [chain_cons h, List.pairwise_cons]
      refine ⟨fun b hb => ?_, ih⟩
      have hp := nxt_pos (P := P) (occ := occ) (d := e) (by tauto)
      exact lt_of_lt_of_le hp.2.1 (chain_lb (P := P) (occ := occ) (M := M) _ b hb)

lemma chain_occ : ∀ (d : ℕ), occ d = true → ∀ x ∈ chain P occ M d, occ x = true := by
  intro d
  induction d using chain.induct P occ M with
  | case1 e d h => intro hocc x hx; rw [chain_single h] at hx; simp at hx; subst hx; exact hocc
  | case2 e d h hmm ih =>
      intro hocc x hx
      rw [chain_cons h, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hocc
      · exact ih (nxt_pos (P := P) (occ := occ) (d := e) (by tauto)).1 x hx

/-- Nothing occupied within `P` above a point of the walk escapes it. -/
lemma chain_forward (hM : ∀ e, occ e = true → e ≤ M) :
    ∀ (d : ℕ), ∀ x ∈ chain P occ M d, ∀ e, occ e = true → x < e → e < x + P →
      e ∈ chain P occ M d := by
  intro d
  induction d using chain.induct P occ M with
  | case1 c d h =>
      intro x hx e he hxe hep
      rw [chain_single h] at hx ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      subst hx
      rcases h with h | h
      · exact absurd he (by rw [nxt_zero h e hxe hep]; simp)
      · have := hM e he; omega
  | case2 c d h hmm ih =>
      intro x hx e he hxe hep
      have hp := nxt_pos (P := P) (occ := occ) (d := c) (by tauto)
      rw [chain_cons h, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · rcases Nat.lt_or_ge e (nxt P occ x) with hlt | hge
        · exact absurd he (by rw [hp.2.2.2 e hxe hlt]; simp)
        · rcases Nat.eq_or_lt_of_le hge with heq | hlt
          · exact Or.inr (heq ▸ mem_chain_self _)
          · exact Or.inr (ih (nxt P occ x) (mem_chain_self _) e he hlt (by omega))
      · exact Or.inr (ih x hx e he hxe hep)

/-- The walk has no gaps. -/
lemma chain_nogap :
    ∀ (d : ℕ), ∀ x ∈ chain P occ M d, ∀ e, occ e = true → d ≤ e → e ≤ x →
      e ∈ chain P occ M d := by
  intro d
  induction d using chain.induct P occ M with
  | case1 c d h =>
      intro x hx e he hde hex
      rw [chain_single h] at hx ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      omega
  | case2 c d h hmm ih =>
      intro x hx e he hde hex
      have hp := nxt_pos (P := P) (occ := occ) (d := c) (by tauto)
      rw [chain_cons h, List.mem_cons] at hx ⊢
      rcases Nat.eq_or_lt_of_le hde with rfl | hlt
      · exact Or.inl rfl
      · refine Or.inr (ih x ?_ e he ?_ hex)
        · rcases hx with rfl | hx
          · omega
          · exact hx
        · rcases Nat.lt_or_ge e (nxt P occ c) with hlt' | hge
          · exact absurd he (by rw [hp.2.2.2 e hlt hlt']; simp)
          · exact hge

/-- Every point of a walk but its first has an occupied point just below it. -/
lemma mem_chain_pred :
    ∀ (d : ℕ), occ d = true → ∀ x ∈ chain P occ M d, x ≠ d →
      ∃ y, occ y = true ∧ y < x ∧ x < y + P := by
  intro d
  induction d using chain.induct P occ M with
  | case1 c d h =>
      intro hocc x hx hne
      rw [chain_single h] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      exact absurd hx hne
  | case2 c d h hmm ih =>
      intro hocc x hx hne
      have hp := nxt_pos (P := P) (occ := occ) (d := c) (by tauto)
      rw [chain_cons h, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd rfl hne
      · by_cases hx' : x = nxt P occ c
        · exact ⟨c, hocc, by omega, by omega⟩
        · exact ih hp.1 x hx hx'

/-- A walk is a suffix of any walk it starts inside. -/
lemma chain_subset :
    ∀ (d : ℕ), ∀ e ∈ chain P occ M d, ∀ x ∈ chain P occ M e, x ∈ chain P occ M d := by
  intro d
  induction d using chain.induct P occ M with
  | case1 c d h =>
      intro e he x hx
      rw [chain_single h] at he ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
      subst he
      rw [chain_single h] at hx
      simpa using hx
  | case2 c d h hmm ih =>
      intro e he x hx
      rw [chain_cons h, List.mem_cons] at he ⊢
      rcases he with rfl | he
      · rw [chain_cons h, List.mem_cons] at hx
        exact hx
      · exact Or.inr (ih e he x hx)

/-- **Every occupied point lies on the walk from a block start.** -/
lemma exists_start (hM : ∀ e, occ e = true → e ≤ M) (hocc0 : occ 0 = false) :
    ∀ d, occ d = true → ∃ s, isStart P occ s = true ∧ d ∈ chain P occ M s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      intro hd
      by_cases hs : isStart P occ d = true
      · exact ⟨d, hs, mem_chain_self d⟩
      · obtain ⟨e₀, he₀, he₀', he₀''⟩ : ∃ e, e < d ∧ d < e + P ∧ occ e = true := by
          by_contra hc
          push_neg at hc
          refine hs ((isStart_iff hocc0 d).mpr ⟨hd, fun e h1 h2 => ?_⟩)
          by_contra hcc
          exact absurd (hc e h1 h2) (by simpa using hcc)
        have hne : ((Finset.range d).filter fun e => occ e = true ∧ d < e + P).Nonempty :=
          ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he₀, he₀'', he₀'⟩⟩
        obtain ⟨hmem1, hocce, hgap⟩ :=
          Finset.mem_filter.mp (Finset.max'_mem _ hne)
        have hlt : ((Finset.range d).filter fun e => occ e = true ∧ d < e + P).max' hne < d :=
          Finset.mem_range.mp hmem1
        set e := ((Finset.range d).filter fun e => occ e = true ∧ d < e + P).max' hne with he
        have hnone : ∀ f, e < f → f < d → occ f = false := by
          intro f h1 h2
          by_contra hcf
          have : f ≤ e := Finset.le_max' _ f
            (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, by simpa using hcf, by omega⟩)
          omega
        have hnxt : nxt P occ e = d := by
          by_cases h0 : nxt P occ e = 0
          · exact absurd hd (by rw [nxt_zero h0 d hlt hgap]; simp)
          · have hp := nxt_pos (P := P) (occ := occ) (d := e) h0
            rcases lt_trichotomy (nxt P occ e) d with hc | hc | hc
            · exact absurd hp.1 (by rw [hnone _ hp.2.1 hc]; simp)
            · exact hc
            · exact absurd hd (by rw [hp.2.2.2 d hlt hc]; simp)
        obtain ⟨s, hs', hmem'⟩ := ih e hlt hocce
        refine ⟨s, hs', chain_subset (P := P) (occ := occ) (M := M) s e hmem' d ?_⟩
        have hdM : d ≤ M := hM d hd
        rw [chain_cons (show ¬ (nxt P occ e = 0 ∨ M ≤ e) by rw [hnxt]; omega), hnxt]
        exact List.mem_cons_of_mem _ (mem_chain_self d)

/-- **A point lies on only one walk from a block start.** -/
lemma start_unique (hocc0 : occ 0 = false) {s s' d : ℕ}
    (hs : isStart P occ s = true) (hs' : isStart P occ s' = true)
    (h : d ∈ chain P occ M s) (h' : d ∈ chain P occ M s') : s = s' := by
  have key : ∀ a b : ℕ, isStart P occ a = true → isStart P occ b = true →
      d ∈ chain P occ M a → d ∈ chain P occ M b → a < b → False := by
    intro a b ha hb hda hdb hab
    obtain ⟨hboc, hbgap⟩ := (isStart_iff hocc0 b).mp hb
    obtain ⟨haoc, -⟩ := (isStart_iff hocc0 a).mp ha
    have hbd : b ≤ d := chain_lb (P := P) (occ := occ) (M := M) b d hdb
    have hbmem : b ∈ chain P occ M a :=
      chain_nogap (P := P) (occ := occ) (M := M) a d hda b hboc (by omega) hbd
    obtain ⟨y, hy, hy1, hy2⟩ :=
      mem_chain_pred (P := P) (occ := occ) (M := M) a haoc b hbmem (by omega)
    exact absurd hy (by rw [hbgap y hy1 hy2]; simp)
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · exact (key s s' hs hs' h h' hlt).elim
  · exact heq
  · exact (key s' s hs' hs h' h hgt).elim

/-- **Points off a walk are `P` away from every point on it.** -/
lemma chain_sep (hM : ∀ e, occ e = true → e ≤ M) (hocc0 : occ 0 = false) {s : ℕ}
    (hs : isStart P occ s = true) {x e : ℕ} (hx : x ∈ chain P occ M s) (he : occ e = true)
    (hnot : e ∉ chain P occ M s) : x + P ≤ e ∨ e + P ≤ x := by
  obtain ⟨hsocc, hsgap⟩ := (isStart_iff hocc0 s).mp hs
  have hsx : s ≤ x := chain_lb (P := P) (occ := occ) (M := M) s x hx
  rcases lt_trichotomy e x with hlt | rfl | hgt
  · right
    by_contra hc
    rcases Nat.lt_or_ge e s with hes | hes
    · exact absurd he (by rw [hsgap e hes (by omega)]; simp)
    · exact hnot (chain_nogap (P := P) (occ := occ) (M := M) s x hx e he hes (by omega))
  · exact absurd hx hnot
  · left
    by_contra hc
    exact hnot (chain_forward hM s x hx e he hgt (by omega))

end Lax888481Proofs.BlockWalk
