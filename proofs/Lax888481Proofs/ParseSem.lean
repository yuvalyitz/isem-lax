import Lax888481Proofs.ParseModel
import Lax888481.SatVariant
import Lax888481.Exact34Encoding

/-!
The parser's output, and what it means.

An accepted formula is written out as Construction 2's word: each literal by the position
of the first occurrence of its variable — a dense renaming, which keeps the
variable count below the number of literal slots however sparse the indices in the
encoding were — its sign, and the number of earlier occurrences of its variable.
-/

namespace Lax888481Proofs.ParseSem

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime
open Lax888481.SatVariant Lax888481.Exact34Encoding Lax888481Proofs.ParseModel

/-- The name of literal `k`: where its variable first occurs. -/
def nameOf (vs : List ℕ) (k : ℕ) : ℕ := vs.idxOf (vs.getD k 0)

/-- Which occurrence of its variable literal `k` is. -/
def appOf (vs : List ℕ) (k : ℕ) : ℕ := (vs.take k).count (vs.getD k 0)

/-- Construction 2's word. -/
def word (vs ss : List ℕ) (C : ℕ) : List ℕ :=
  [vs.length, C] ++ (List.range vs.length).flatMap fun k => [nameOf vs k, ss.getD k 0, appOf vs k]

/-! ### Reading the Word -/

lemma triples_length (f : ℕ → List ℕ) (hf : ∀ k, (f k).length = 3) (N : ℕ) :
    ((List.range N).flatMap f).length = 3 * N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hf]; omega

lemma triples_getD (f : ℕ → List ℕ) (hf : ∀ k, (f k).length = 3) (N k r : ℕ) (hk : k < N)
    (hr : r < 3) : ((List.range N).flatMap f).getD (3 * k + r) 0 = (f k).getD r 0 := by
  induction N with
  | zero => omega
  | succ N ih =>
      rw [List.range_succ, List.flatMap_append]
      have hlen := triples_length f hf N
      rcases Nat.lt_or_ge k N with h | h
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; omega)]; exact ih h
      · have : k = N := by omega
        subst this
        rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
        simp

variable (vs ss : List ℕ) (C : ℕ)

lemma word_length : (word vs ss C).length = 2 + 3 * vs.length := by
  simp only [word, List.length_append, List.length_cons, List.length_nil]
  rw [triples_length _ (fun _ => rfl)]

lemma word_varCount : varCount (word vs ss C) = vs.length := rfl
lemma word_clauseCount : clauseCount (word vs ss C) = C := rfl

lemma word_entry (k r : ℕ) (hk : k < vs.length) (hr : r < 3) :
    (word vs ss C).getD (2 + 3 * k + r) 0 = [nameOf vs k, ss.getD k 0, appOf vs k].getD r 0 := by
  have : 2 + 3 * k + r = (3 * k + r) + 2 := by omega
  rw [word, this]
  show ((List.range vs.length).flatMap _).getD (3 * k + r) 0 = _
  exact triples_getD _ (fun _ => rfl) _ _ _ hk hr

lemma word_litVar (hC : vs.length = 3 * C) (c h : ℕ) (hc : c < C) (hh : h < 3) :
    litVar (word vs ss C) c h = nameOf vs (3 * c + h) := by
  have := word_entry vs ss C (3 * c + h) 0 (by omega) (by omega)
  rw [litVar]; rw [show 2 + 9 * c + 3 * h = 2 + 3 * (3 * c + h) + 0 by omega, this]; rfl

lemma word_litSign (hC : vs.length = 3 * C) (c h : ℕ) (hc : c < C) (hh : h < 3) :
    litSign (word vs ss C) c h = ss.getD (3 * c + h) 0 := by
  have := word_entry vs ss C (3 * c + h) 1 (by omega) (by omega)
  rw [litSign]; rw [show 2 + 9 * c + 3 * h + 1 = 2 + 3 * (3 * c + h) + 1 by omega, this]; rfl

lemma word_litApp (hC : vs.length = 3 * C) (c h : ℕ) (hc : c < C) (hh : h < 3) :
    litApp (word vs ss C) c h = appOf vs (3 * c + h) := by
  have := word_entry vs ss C (3 * c + h) 2 (by omega) (by omega)
  rw [litApp]; rw [show 2 + 9 * c + 3 * h + 2 = 2 + 3 * (3 * c + h) + 2 by omega, this]; rfl

/-! ### Names and Occurrence Indices -/

section names
variable {vs}

lemma getD_mem {k : ℕ} (hk : k < vs.length) : vs.getD k 0 ∈ vs := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

lemma nameOf_lt {k : ℕ} (hk : k < vs.length) : nameOf vs k < vs.length :=
  List.idxOf_lt_length_of_mem (getD_mem hk)

lemma getD_idxOf {v : ℕ} (hv : v ∈ vs) : vs.getD (vs.idxOf v) 0 = v := by
  have h := List.getElem?_idxOf hv
  rw [List.getD_eq_getElem?_getD, h]; rfl

lemma getD_nameOf {k : ℕ} (hk : k < vs.length) : vs.getD (nameOf vs k) 0 = vs.getD k 0 :=
  getD_idxOf (getD_mem hk)

lemma count_take_succ {k : ℕ} (hk : k < vs.length) (v : ℕ) :
    (vs.take (k + 1)).count v = (vs.take k).count v + if vs.getD k 0 = v then 1 else 0 := by
  rw [List.take_succ, List.count_append, List.getElem?_eq_getElem hk,
    List.getD_eq_getElem _ _ hk, Option.toList_some, List.count_singleton]
  by_cases h : vs[k] = v
  · simp [h]
  · have h' : ¬ (vs[k] == v) = true := by simpa using h
    simp [h, h']

lemma count_take_lt {k k' : ℕ} (h : k < k') (hk' : k' ≤ vs.length) :
    (vs.take k).count (vs.getD k 0) < (vs.take k').count (vs.getD k 0) := by
  have h1 := count_take_succ (vs := vs) (k := k) (by omega) (vs.getD k 0)
  have h2 : (vs.take (k + 1)).count (vs.getD k 0) ≤ (vs.take k').count (vs.getD k 0) :=
    (List.take_prefix_take_left (l := vs) (show k + 1 ≤ k' by omega)).sublist.count_le _
  rw [if_pos rfl] at h1; omega

lemma appOf_lt {k : ℕ} (hk : k < vs.length) (hcnt : ∀ v ∈ vs, vs.count v ≤ 4) :
    appOf vs k < 4 := by
  have h1 := count_take_lt (vs := vs) (k := k) (k' := vs.length) hk (le_refl _)
  rw [List.take_length] at h1
  have := hcnt _ (getD_mem hk)
  unfold appOf
  omega

lemma name_app_inj {k k' : ℕ} (hk : k < vs.length) (hk' : k' < vs.length)
    (hn : nameOf vs k = nameOf vs k') (ha : appOf vs k = appOf vs k') : k = k' := by
  have hv : vs.getD k 0 = vs.getD k' 0 := by
    rw [← getD_nameOf hk, ← getD_nameOf hk', hn]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := count_take_lt (vs := vs) h (by omega)
    unfold appOf at ha; rw [← hv] at ha; omega
  · have := count_take_lt (vs := vs) h (by omega)
    unfold appOf at ha; rw [hv] at ha; omega

end names

/-- **The word is well formed.** -/
theorem word_wellFormed (hC : vs.length = 3 * C) (hcnt : ∀ v ∈ vs, vs.count v ≤ 4) :
    WellFormed (word vs ss C) where
  length_eq := by rw [word_length, word_clauseCount, hC]; omega
  var_lt := fun c hc h hh => by
    rw [word_clauseCount] at hc
    rw [word_litVar vs ss C hC c h hc hh, word_varCount]
    exact nameOf_lt (by omega)
  app_lt := fun c hc h hh => by
    rw [word_clauseCount] at hc
    rw [word_litApp vs ss C hC c h hc hh]
    exact appOf_lt (by omega) hcnt
  var_le := by rw [word_varCount, word_clauseCount, hC]
  app_inj := fun c hc h hh c' hc' h' hh' hv ha => by
    rw [word_clauseCount] at hc hc'
    rw [word_litVar vs ss C hC c h hc hh, word_litVar vs ss C hC c' h' hc' hh'] at hv
    rw [word_litApp vs ss C hC c h hc hh, word_litApp vs ss C hC c' h' hc' hh'] at ha
    have := name_app_inj (vs := vs) (by omega) (by omega) hv ha
    omega

/-! ### Satisfiability -/

def dflt : Literal := ⟨0, false⟩

def litsOf (F : Formula) : List Literal := F.flatMap id
def vsOf (F : Formula) : List ℕ := (litsOf F).map Literal.index
def ssOf (F : Formula) : List ℕ := (litsOf F).map fun l => if l.positive then 1 else 0

lemma litsOf_length {F : Formula} (hF : ∀ c ∈ F, c.length = 3) : (litsOf F).length = 3 * F.length := by
  induction F with
  | nil => rfl
  | cons c t ih =>
      have := hF c List.mem_cons_self
      have := ih fun c' hc' => hF c' (List.mem_cons_of_mem _ hc')
      simp only [litsOf, List.flatMap_cons, List.length_append, id, List.length_cons] at *
      omega

lemma vsOf_getD (F : Formula) (k : ℕ) : (vsOf F).getD k 0 = ((litsOf F).getD k dflt).index := by
  simp only [vsOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (litsOf F)[k]? <;> rfl

lemma ssOf_getD (F : Formula) (k : ℕ) :
    (ssOf F).getD k 0 = if ((litsOf F).getD k dflt).positive then 1 else 0 := by
  simp only [ssOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (litsOf F)[k]? <;> rfl

lemma all_any_iff {F : Formula} (hF : ∀ c ∈ F, c.length = 3) (Q : Literal → Prop) :
    (∀ c ∈ F, ∃ l ∈ c, Q l) ↔
      ∀ c < F.length, ∃ h < 3, Q ((litsOf F).getD (3 * c + h) dflt) := by
  induction F with
  | nil => simp
  | cons C t ih =>
      have ih' := ih fun c' hc' => hF c' (List.mem_cons_of_mem _ hc')
      obtain ⟨a, b, e, rfl⟩ : ∃ a b e, C = [a, b, e] := by
        match C, hF C List.mem_cons_self with
        | [a, b, e], _ => exact ⟨a, b, e, rfl⟩
      have hsh : ∀ c h, (litsOf ([a, b, e] :: t)).getD (3 * (c + 1) + h) dflt
          = (litsOf t).getD (3 * c + h) dflt := by
        intro c h
        have : 3 * (c + 1) + h = (3 * c + h) + 3 := by omega
        rw [this]; rfl
      constructor
      · intro H c hc
        rcases c with _ | c
        · obtain ⟨l, hl, hq⟩ := H _ List.mem_cons_self
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl | rfl
          · exact ⟨0, by omega, hq⟩
          · exact ⟨1, by omega, hq⟩
          · exact ⟨2, by omega, hq⟩
        · obtain ⟨h, hh, hq⟩ := ih'.mp (fun c' hc' => H c' (List.mem_cons_of_mem _ hc')) c
            (by simpa using hc)
          exact ⟨h, hh, by rw [hsh]; exact hq⟩
      · intro H c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · obtain ⟨h, hh, hq⟩ := H 0 (by simp)
          have : h = 0 ∨ h = 1 ∨ h = 2 := by omega
          rcases this with rfl | rfl | rfl
          · exact ⟨a, by simp, hq⟩
          · exact ⟨b, by simp, hq⟩
          · exact ⟨e, by simp, hq⟩
        · refine ih'.mpr (fun c' hc' => ?_) c hc
          obtain ⟨h, hh, hq⟩ := H (c' + 1) (by simpa using hc')
          exact ⟨h, hh, by rw [hsh] at hq; exact hq⟩

lemma lit_iff (l : Literal) (b : Bool) :
    (if l.positive then b else !b) = true ↔
      (((if l.positive then 1 else 0 : ℕ) = 1) = (b = true)) := by
  cases l.positive <;> cases b <;> simp

lemma eval_iff (F : Formula) (ρ : Assignment) :
    eval F ρ = true ↔ ∀ c ∈ F, ∃ l ∈ c, l.eval ρ = true := by
  simp [eval]

/-- **The word is satisfiable exactly when the formula is.** -/
theorem sat_iff {F : Formula} (hF : ∀ c ∈ F, c.length = 3) :
    (∃ τ, Satisfies (word (vsOf F) (ssOf F) F.length) τ) ↔ Satisfiable F := by
  have hC : (vsOf F).length = 3 * F.length := by rw [vsOf, List.length_map, litsOf_length hF]
  have key : ∀ (τ : ℕ → Bool) (ρ : Assignment),
      (∀ k < (vsOf F).length, τ (nameOf (vsOf F) k) = ρ ((vsOf F).getD k 0)) →
      (Satisfies (word (vsOf F) (ssOf F) F.length) τ ↔ eval F ρ = true) := by
    intro τ ρ hτ
    rw [eval_iff, all_any_iff hF, Satisfies, word_clauseCount]
    refine forall₂_congr fun c hc => exists_congr fun h => and_congr_right fun hh => ?_
    rw [word_litSign _ _ _ hC c h hc hh, word_litVar _ _ _ hC c h hc hh, hτ _ (by omega),
      ssOf_getD, vsOf_getD, Literal.eval]
    exact (lit_iff _ _).symm
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨fun v => τ ((vsOf F).idxOf v), (key τ _ fun k _ => rfl).mp hτ⟩
  · rintro ⟨ρ, hρ⟩
    refine ⟨fun i => ρ ((vsOf F).getD i 0), (key _ ρ fun k hk => ?_).mpr hρ⟩
    show ρ _ = ρ _
    rw [getD_nameOf hk]

/-! ### The Parser -/

lemma occurrences_eq (F : Formula) (i : ℕ) : occurrences F i = (vsOf F).count i := by
  unfold occurrences vsOf litsOf
  induction F with
  | nil => rfl
  | cons C t ih =>
      simp only [List.flatMap_cons, List.length_append, id, List.map_append,
        List.count_append] at ih ⊢
      rw [ih]; congr 1
      induction C with
      | nil => rfl
      | cons l C ihC =>
          by_cases hl : l.index = i
          · simp [List.filter_cons, hl, ihC]
          · have : ¬ (l.index == i) = true := by simpa using hl
            simp [List.filter_cons, hl, ihC]

instance (vs : List ℕ) : Decidable (∀ v ∈ vs, vs.count v ≤ 4) := List.decidableBAll _ _

/-- The parser, on bits. -/
def parseBits (w : Word) : List ℕ :=
  let s := run init w
  if s.ph = 4 ∧ ∀ v ∈ vsOf s.done, (vsOf s.done).count v ≤ 4 then
    word (vsOf s.done) (ssOf s.done) s.done.length
  else []

lemma nil_not_sat : ([] : List ℕ) ∉ Lax888481.Exact34Encoding.Satisfiable := by
  rintro ⟨hwf, -⟩
  have := hwf.length_eq
  simp only [List.length_nil] at this
  omega

/-- **The parser is correct.** -/
theorem parseBits_correct (w : Word) :
    w ∈ SAT34 ↔ parseBits w ∈ Lax888481.Exact34Encoding.Satisfiable := by
  constructor
  · rintro ⟨F, rfl, ⟨h3, h4⟩, hsat⟩
    obtain ⟨hph, hdone⟩ := accept_complete F h3
    have hcnt : ∀ v ∈ vsOf F, (vsOf F).count v ≤ 4 := fun v hv => by
      rw [← occurrences_eq]; exact h4 v hv
    have hC : (vsOf F).length = 3 * F.length := by rw [vsOf, List.length_map, litsOf_length h3]
    rw [parseBits]; simp only [hph, hdone]
    rw [if_pos ⟨trivial, hcnt⟩]
    exact ⟨word_wellFormed _ _ _ hC hcnt, (sat_iff h3).mpr hsat⟩
  · intro h
    unfold parseBits at h
    simp only at h
    split_ifs at h with hc
    · obtain ⟨hph, hcnt⟩ := hc
      obtain ⟨henc, h3⟩ := accept_sound hph
      refine ⟨_, henc, ⟨h3, fun i hi => ?_⟩, (sat_iff h3).mp h.2⟩
      rw [occurrences_eq]; exact hcnt i hi
    · exact absurd h nil_not_sat

end Lax888481Proofs.ParseSem
