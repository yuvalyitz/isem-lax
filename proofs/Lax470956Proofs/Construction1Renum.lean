import Lax470956Proofs.Construction1Join
import Lax470956Proofs.Renumbering

/-!
Construction 1's renumbering: the machine and job correspondences.
-/

namespace Lax470956Proofs.Construction1Renum

open Lax470956.Construction1 Lax470956.MulticolouredClique
open Lax470956Proofs.TypedIsem Lax470956Proofs.TypedMcc
open Lax470956Proofs.Construction1Typed.Construction1
open Lax470956Proofs.Construction1Join Lax470956Proofs.Construction1Slots
open Lax470956Proofs.Construction1Index

variable (G : Lax470956.MulticolouredClique.Instance)

/-! ### Machines -/

/-- The machine numbering: the validation machine last, the edge selection machines by
their colour pair. -/
def machFun : Machine G.colours → Fin (nMach G)
  | none => ⟨G.colours.choose 2, Nat.lt_succ_self _⟩
  | some c => ⟨pairIdx (c.lo : ℕ) (c.hi : ℕ),
      Nat.lt_succ_of_lt (pairIdx_lt (by exact c.lo_lt_hi) c.hi.isLt)⟩

lemma machFun_inj : Function.Injective (machFun G) := by
  intro a b hab
  match a, b with
  | none, none => rfl
  | none, some c =>
      exact absurd (Fin.val_eq_of_eq hab).symm
        (Nat.ne_of_lt (pairIdx_lt (by exact c.lo_lt_hi) c.hi.isLt))
  | some c, none =>
      exact absurd (Fin.val_eq_of_eq hab)
        (Nat.ne_of_lt (pairIdx_lt (by exact c.lo_lt_hi) c.hi.isLt))
  | some c, some c' =>
      have h := Fin.val_eq_of_eq hab
      simp only [machFun] at h
      obtain ⟨h1, h2⟩ := pairIdx_inj (by exact c.lo_lt_hi) (by exact c'.lo_lt_hi) h
      exact congrArg some (ColorPair.eq_of (Fin.ext h1) (Fin.ext h2))

lemma card_machine_eq : Fintype.card (Machine G.colours) = nMach G := by
  rw [card_machine]
  rfl

/-- The machines of the two presentations correspond. -/
noncomputable def machEquiv : Machine G.colours ≃ Fin (nMach G) :=
  Equiv.ofBijective (machFun G)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨machFun_inj G, by rw [card_machine_eq, Fintype.card_fin]⟩)

@[simp] lemma machEquiv_apply (i : Machine G.colours) : machEquiv G i = machFun G i := rfl

/-! ### Jobs -/

/-- A vertex of the paper's instance, as a number. Its type is the archive's
`Fin G.vertices` by definition, but not syntactically, so the coercion is named. -/
def vnum (v : (ofInstance G).V) : ℕ := (show Fin G.vertices from v).val

lemma vnum_lt (v : (ofInstance G).V) : vnum G v < G.vertices :=
  (show Fin G.vertices from v).isLt

lemma vnum_inj {u v : (ofInstance G).V} (h : vnum G u = vnum G v) : u = v :=
  show (show Fin G.vertices from u) = (show Fin G.vertices from v) from Fin.ext h

/-- An edge job, as a pair of the archive's vertices. -/
def epair (e : EJob (ofInstance G)) : Fin G.vertices × Fin G.vertices :=
  (show Fin G.vertices from e.1.1, show Fin G.vertices from e.1.2)

lemma edgeList_nodup : (edgeList G).Nodup :=
  List.Nodup.filter _ (List.Nodup.product (List.nodup_finRange _) (List.nodup_finRange _))

lemma mem_edgeList (p : Fin G.vertices × Fin G.vertices) :
    p ∈ edgeList G ↔ ((G.colour p.1 : ℕ) < (G.colour p.2 : ℕ) ∧ G.graph.Adj p.1 p.2) := by
  simp only [edgeList, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases p with ⟨u, v⟩
    exact List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩

lemma epair_mem (e : EJob (ofInstance G)) : epair G e ∈ edgeList G :=
  (mem_edgeList G (epair G e)).mpr ⟨e.2.1, e.2.2⟩

/-- Where an edge job sits in the enumeration of the edges. -/
noncomputable def eidx (e : EJob (ofInstance G)) : ℕ := (edgeList G).idxOf (epair G e)

lemma eidx_lt (e : EJob (ofInstance G)) : eidx G e < nEJob G :=
  List.idxOf_lt_length_of_mem (epair_mem G e)

lemma getElem_eidx (e : EJob (ofInstance G)) :
    (edgeList G)[eidx G e]'(eidx_lt G e) = epair G e := List.getElem_idxOf _

/-- The job numbering: the vertex jobs, then the colour combination jobs in their slots,
then the edge jobs in theirs. -/
noncomputable def jobNum : Job (ofInstance G) → ℕ
  | Sum.inl x => vIdx G (vnum G x.1) (x.2 : ℕ)
  | Sum.inr (Sum.inl e) => eIdx G (eidx G e)
  | Sum.inr (Sum.inr x) => cIdx G (x.1.1.lo : ℕ) (x.1.1.hi : ℕ) (vnum G x.1.2)

lemma jobNum_lt (j : Job (ofInstance G)) : jobNum G j < nJobs G := by
  match j with
  | Sum.inl x =>
      have h := vIdx_lt (G := G) (v := vnum G x.1) (l := (x.2 : ℕ)) (vnum_lt G x.1) x.2.isLt
      simp only [jobNum, nJobs]
      omega
  | Sum.inr (Sum.inl e) =>
      exact (eIdx_mem (G := G) (eidx_lt G e)).2
  | Sum.inr (Sum.inr x) =>
      have h := cIdx_mem (G := G) (a := (x.1.1.lo : ℕ)) (b := (x.1.1.hi : ℕ))
        (z := vnum G x.1.2) x.1.1.lo.isLt x.1.1.hi.isLt (vnum_lt G x.1.2)
      simp only [jobNum, nJobs]
      omega

/-- The job numbering, as a slot. -/
noncomputable def jobFun (j : Job (ofInstance G)) : Fin (nJobs G) := ⟨jobNum G j, jobNum_lt G j⟩

/-! ### Reading the concept's accessors at a job's slot -/

lemma col_vnum (v : (ofInstance G).V) :
    col (G := G) (vnum G v) = ((ofInstance G).color v : ℕ) := by
  simp only [col, dif_pos (vnum_lt G v)]
  rfl

lemma pos_vnum (v : (ofInstance G).V) : pos (G := G) (vnum G v) = (ord G).π v := by
  simp only [pos, dif_pos (vnum_lt G v)]
  rfl

/-! ### The vertex jobs -/

variable {G}

lemma jobNum_v (x : VJob (ofInstance G)) :
    jobNum G (Sum.inl x) = vIdx G (vnum G x.1) (x.2 : ℕ) := rfl

lemma vslot_lt (x : VJob (ofInstance G)) : jobNum G (Sum.inl x) < nVJob G := by
  rw [jobNum_v]
  exact vIdx_lt (vnum_lt G x.1) x.2.isLt

lemma vjCol_v (x : VJob (ofInstance G)) : vjCol G (jobNum G (Sum.inl x)) = (x.2 : ℕ) := by
  rw [jobNum_v]; exact vjCol_vIdx x.2.isLt

lemma vjVert_v (x : VJob (ofInstance G)) : vjVert G (jobNum G (Sum.inl x)) = vnum G x.1 := by
  rw [jobNum_v]; exact vjVert_vIdx x.2.isLt

/-- The concept's branch test at a vertex slot is the paper's. -/
lemma vtest (x : VJob (ofInstance G)) :
    (vjCol G (jobNum G (Sum.inl x)) = col (G := G) (vjVert G (jobNum G (Sum.inl x))))
      ↔ x.2 = (ofInstance G).color x.1 := by
  rw [vjCol_v, vjVert_v, col_vnum]
  exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

lemma rawProc_v (x : VJob (ofInstance G)) :
    rawProc G (jobNum G (Sum.inl x)) = vP (ofInstance G) x := by
  rw [rawProc, if_pos (vslot_lt x), vP]
  by_cases h : x.2 = (ofInstance G).color x.1
  · rw [if_pos ((vtest x).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((vtest x).mp hc)), if_neg h]

lemma rawDue_v (x : VJob (ofInstance G)) :
    rawDue G (jobNum G (Sum.inl x)) = vD (ofInstance G) (ord G) x := by
  rw [rawDue, if_pos (vslot_lt x), vD, vjVert_v, vjCol_v, pos_vnum, col_vnum]
  by_cases h : x.2 = (ofInstance G).color x.1
  · rw [if_pos (congrArg Fin.val h), if_pos h]
  · rw [if_neg (fun hc => h (Fin.ext hc)), if_neg h]

lemma wtOf_v (x : VJob (ofInstance G)) :
    wtOf G (jobNum G (Sum.inl x)) = vW (ofInstance G) x := by
  rw [wtOf, if_pos (vslot_lt x), vW]
  by_cases h : x.2 = (ofInstance G).color x.1
  · rw [if_pos ((vtest x).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((vtest x).mp hc)), if_neg h, c1_eq]

/-! ### The colour combination jobs -/

lemma jobNum_c (x : CJob (ofInstance G)) :
    jobNum G (Sum.inr (Sum.inr x)) = cIdx G (x.1.1.lo : ℕ) (x.1.1.hi : ℕ) (vnum G x.1.2) := rfl

lemma cslot_mem (x : CJob (ofInstance G)) :
    nVJob G ≤ jobNum G (Sum.inr (Sum.inr x)) ∧
      jobNum G (Sum.inr (Sum.inr x)) < nVJob G + nCJob G := by
  rw [jobNum_c]
  exact cIdx_mem x.1.1.lo.isLt x.1.1.hi.isLt (vnum_lt G x.1.2)

lemma cjA_c (x : CJob (ofInstance G)) :
    cjA G (jobNum G (Sum.inr (Sum.inr x)) - nVJob G) = (x.1.1.lo : ℕ) := by
  rw [jobNum_c]; exact cjA_cIdx x.1.1.hi.isLt (vnum_lt G x.1.2)

lemma cjB_c (x : CJob (ofInstance G)) :
    cjB G (jobNum G (Sum.inr (Sum.inr x)) - nVJob G) = (x.1.1.hi : ℕ) := by
  rw [jobNum_c]; exact cjB_cIdx x.1.1.hi.isLt (vnum_lt G x.1.2)

lemma cjZ_c (x : CJob (ofInstance G)) :
    cjZ G (jobNum G (Sum.inr (Sum.inr x)) - nVJob G) = vnum G x.1.2 := by
  rw [jobNum_c]; exact cjZ_cIdx (vnum_lt G x.1.2)

lemma cok (x : CJob (ofInstance G)) : CJobOk G (jobNum G (Sum.inr (Sum.inr x)) - nVJob G) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cjA_c, cjB_c]; exact x.1.1.lo_lt_hi
  · rw [cjB_c]; exact x.1.1.hi.isLt
  · rw [cjZ_c]; exact vnum_lt G x.1.2
  · rw [cjZ_c, cjA_c, cjB_c, col_vnum]
    rcases x.2 with h | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (congrArg Fin.val h)

lemma rawProc_c (x : CJob (ofInstance G)) :
    rawProc G (jobNum G (Sum.inr (Sum.inr x))) = cP (ofInstance G) (ord G) x := by
  rw [rawProc, if_neg (by have := (cslot_mem x).1; omega), if_pos (cslot_mem x).2]
  simp only [if_pos (cok x)]
  rw [cP, cjZ_c, cjA_c, cjB_c, pos_vnum, nG_ofInstance, col_vnum]
  by_cases h : (ofInstance G).color x.1.2 = x.1.1.lo
  · rw [if_pos (congrArg Fin.val h), if_pos h]
  · rw [if_neg (fun hc => h (Fin.ext hc)), if_neg h]

lemma rawDue_c (x : CJob (ofInstance G)) :
    rawDue G (jobNum G (Sum.inr (Sum.inr x))) = cD (ofInstance G) (ord G) x := by
  rw [rawDue, if_neg (by have := (cslot_mem x).1; omega), if_pos (cslot_mem x).2]
  simp only [if_pos (cok x)]
  rw [cD, cjZ_c, cjB_c, pos_vnum, nG_ofInstance, col_vnum, cjA_c]
  by_cases h : (ofInstance G).color x.1.2 = x.1.1.lo
  · rw [if_pos (congrArg Fin.val h), if_pos h]
  · rw [if_neg (fun hc => h (Fin.ext hc)), if_neg h]

lemma wtOf_c (x : CJob (ofInstance G)) :
    wtOf G (jobNum G (Sum.inr (Sum.inr x))) = cW (ofInstance G) (ord G) x := by
  rw [wtOf, if_neg (by have := (cslot_mem x).1; omega), if_pos (cslot_mem x).2]
  simp only [if_pos (cok x)]
  rw [cW, cjZ_c, cjA_c, pos_vnum, nG_ofInstance, col_vnum, c2_eq]
  by_cases h : (ofInstance G).color x.1.2 = x.1.1.lo
  · rw [if_pos (congrArg Fin.val h), if_pos h]
  · rw [if_neg (fun hc => h (Fin.ext hc)), if_neg h]

/-! ### The edge jobs -/

lemma jobNum_e (e : EJob (ofInstance G)) :
    jobNum G (Sum.inr (Sum.inl e)) = eIdx G (eidx G e) := rfl

lemma eslot_mem (e : EJob (ofInstance G)) :
    nVJob G + nCJob G ≤ jobNum G (Sum.inr (Sum.inl e)) ∧
      jobNum G (Sum.inr (Sum.inl e)) < nJobs G := by
  rw [jobNum_e]
  exact eIdx_mem (eidx_lt G e)

lemma eoff (e : EJob (ofInstance G)) :
    jobNum G (Sum.inr (Sum.inl e)) - nVJob G - nCJob G = eidx G e := by
  rw [jobNum_e]; exact eIdx_sub

lemma getElem?_eidx (e : EJob (ofInstance G)) :
    (edgeList G)[eidx G e]? = some (epair G e) := by
  rw [List.getElem?_eq_getElem (eidx_lt G e), getElem_eidx]

lemma ejU_e (e : EJob (ofInstance G)) :
    ejU G (jobNum G (Sum.inr (Sum.inl e)) - nVJob G - nCJob G) = vnum G e.1.1 := by
  rw [eoff, ejU, getElem?_eidx]; rfl

lemma ejV_e (e : EJob (ofInstance G)) :
    ejV G (jobNum G (Sum.inr (Sum.inl e)) - nVJob G - nCJob G) = vnum G e.1.2 := by
  rw [eoff, ejV, getElem?_eidx]; rfl

lemma eok (e : EJob (ofInstance G)) :
    EJobOk G (jobNum G (Sum.inr (Sum.inl e)) - nVJob G - nCJob G) := by
  rw [eoff]; exact eidx_lt G e

lemma rawProc_e (e : EJob (ofInstance G)) :
    rawProc G (jobNum G (Sum.inr (Sum.inl e))) = eP (ofInstance G) (ord G) e := by
  rw [rawProc, if_neg (by have := (eslot_mem e).1; omega),
    if_neg (by have := (eslot_mem e).1; omega)]
  simp only [if_pos (eok e)]
  rw [eP, ejU_e, ejV_e, pos_vnum, pos_vnum, col_vnum, col_vnum]

lemma rawDue_e (e : EJob (ofInstance G)) :
    rawDue G (jobNum G (Sum.inr (Sum.inl e))) = eD (ofInstance G) (ord G) e := by
  rw [rawDue, if_neg (by have := (eslot_mem e).1; omega),
    if_neg (by have := (eslot_mem e).1; omega)]
  simp only [if_pos (eok e)]
  rw [eD, ejU_e, ejV_e, pos_vnum, col_vnum]

lemma wtOf_e (e : EJob (ofInstance G)) :
    wtOf G (jobNum G (Sum.inr (Sum.inl e))) = eW (ofInstance G) (ord G) e := by
  rw [wtOf, if_neg (by have := (eslot_mem e).1; omega),
    if_neg (by have := (eslot_mem e).1; omega)]
  simp only [if_pos (eok e)]
  rw [eW, ejU_e, ejV_e, pos_vnum, pos_vnum, c2_eq, c3_eq]

/-! ### The three families together -/

lemma rawProc_eq (j : Job (ofInstance G)) :
    rawProc G (jobNum G j) = (isem (ofInstance G) (ord G)).p j := by
  match j with
  | Sum.inl x => exact rawProc_v x
  | Sum.inr (Sum.inl e) => exact rawProc_e e
  | Sum.inr (Sum.inr x) => exact rawProc_c x

lemma rawDue_eq (j : Job (ofInstance G)) :
    rawDue G (jobNum G j) = (isem (ofInstance G) (ord G)).d j := by
  match j with
  | Sum.inl x => exact rawDue_v x
  | Sum.inr (Sum.inl e) => exact rawDue_e e
  | Sum.inr (Sum.inr x) => exact rawDue_c x

lemma wt_eq (j : Job (ofInstance G)) :
    wtOf G (jobNum G j) = (isem (ofInstance G) (ord G)).w j := by
  match j with
  | Sum.inl x => exact wtOf_v x
  | Sum.inr (Sum.inl e) => exact wtOf_e e
  | Sum.inr (Sum.inr x) => exact wtOf_c x

lemma procOf_eq (j : Job (ofInstance G)) :
    procOf G (jobNum G j) = (isem (ofInstance G) (ord G)).p j := by
  have h1 := rawProc_eq j
  have h2 := rawDue_eq j
  have hp := (isem (ofInstance G) (ord G)).p_pos j
  have hd := (isem (ofInstance G) (ord G)).p_le_d j
  simp only [procOf, h1, h2]
  omega

lemma dueOf_eq (j : Job (ofInstance G)) :
    dueOf G (jobNum G j) = (isem (ofInstance G) (ord G)).d j := by
  have h2 := rawDue_eq j
  have hp := (isem (ofInstance G) (ord G)).p_pos j
  have hd := (isem (ofInstance G) (ord G)).p_le_d j
  simp only [dueOf, h2]
  omega

/-! ### Injectivity -/

lemma jobNum_inj : Function.Injective (jobNum G) := by
  intro a b hab
  match a, b with
  | Sum.inl x, Sum.inl y =>
      have h1 : vnum G x.1 = vnum G y.1 := by rw [← vjVert_v x, hab, vjVert_v y]
      have h2 : (x.2 : ℕ) = (y.2 : ℕ) := by rw [← vjCol_v x, hab, vjCol_v y]
      exact congrArg Sum.inl (Prod.ext (vnum_inj G h1) (Fin.ext h2))
  | Sum.inl x, Sum.inr (Sum.inl e) =>
      refine absurd hab ?_
      have h1 := vslot_lt x
      have h2 := (eslot_mem e).1
      omega
  | Sum.inl x, Sum.inr (Sum.inr y) =>
      refine absurd hab ?_
      have h1 := vslot_lt x
      have h2 := (cslot_mem y).1
      omega
  | Sum.inr (Sum.inl e), Sum.inl y =>
      refine absurd hab ?_
      have h1 := vslot_lt y
      have h2 := (eslot_mem e).1
      omega
  | Sum.inr (Sum.inr x), Sum.inl y =>
      refine absurd hab ?_
      have h1 := vslot_lt y
      have h2 := (cslot_mem x).1
      omega
  | Sum.inr (Sum.inl e), Sum.inr (Sum.inr y) =>
      refine absurd hab ?_
      have h1 := (eslot_mem e).1
      have h2 := (cslot_mem y).2
      omega
  | Sum.inr (Sum.inr x), Sum.inr (Sum.inl f) =>
      refine absurd hab ?_
      have h1 := (eslot_mem f).1
      have h2 := (cslot_mem x).2
      omega
  | Sum.inr (Sum.inl e), Sum.inr (Sum.inl f) =>
      have hq : eidx G e = eidx G f := by
        have := hab
        rw [jobNum_e, jobNum_e, eIdx, eIdx] at this
        omega
      have hp : epair G e = epair G f := (List.idxOf_inj (epair_mem G e)).mp hq
      exact congrArg (fun t => Sum.inr (Sum.inl t))
        (Subtype.ext (Prod.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)))
  | Sum.inr (Sum.inr x), Sum.inr (Sum.inr y) =>
      have hlo : (x.1.1.lo : ℕ) = (y.1.1.lo : ℕ) := by rw [← cjA_c x, hab, cjA_c y]
      have hhi : (x.1.1.hi : ℕ) = (y.1.1.hi : ℕ) := by rw [← cjB_c x, hab, cjB_c y]
      have hz : vnum G x.1.2 = vnum G y.1.2 := by rw [← cjZ_c x, hab, cjZ_c y]
      exact congrArg (fun t => Sum.inr (Sum.inr t))
        (Subtype.ext (Prod.ext (ColorPair.eq_of (Fin.ext hlo) (Fin.ext hhi)) (vnum_inj G hz)))

lemma jobFun_inj : Function.Injective (jobFun G) :=
  fun _ _ h => jobNum_inj (Fin.val_eq_of_eq h)

/-! ### Eligibility -/

def machFun_none_val : ((machFun G none : Fin (nMach G)) : ℕ) = G.colours.choose 2 := rfl

def machFun_some_val (c : ColorPair G.colours) :
    ((machFun G (some c) : Fin (nMach G)) : ℕ) = pairIdx (c.lo : ℕ) (c.hi : ℕ) := rfl

lemma pairIdx_ne_val (c : ColorPair G.colours) :
    pairIdx (c.lo : ℕ) (c.hi : ℕ) ≠ G.colours.choose 2 :=
  Nat.ne_of_lt (pairIdx_lt (by exact c.lo_lt_hi) c.hi.isLt)

lemma eligOf_v_own (x : VJob (ofInstance G)) (h : x.2 = (ofInstance G).color x.1) :
    eligOf G (jobNum G (Sum.inl x)) = [validation G] := by
  rw [eligOf, if_pos (vslot_lt x), if_pos ((vtest x).mpr h)]

lemma eligOf_v_other (x : VJob (ofInstance G)) (h : ¬ x.2 = (ofInstance G).color x.1) :
    eligOf G (jobNum G (Sum.inl x)) =
      [validation G,
        pairIdx (min (x.2 : ℕ) (((ofInstance G).color x.1 : ℕ)))
          (max (x.2 : ℕ) (((ofInstance G).color x.1 : ℕ)))] := by
  rw [eligOf, if_pos (vslot_lt x), if_neg (fun hc => h ((vtest x).mp hc)), vjCol_v, vjVert_v,
    col_vnum]

lemma eligOf_c' (x : CJob (ofInstance G)) :
    eligOf G (jobNum G (Sum.inr (Sum.inr x))) = [pairIdx (x.1.1.lo : ℕ) (x.1.1.hi : ℕ)] := by
  rw [eligOf, if_neg (by have := (cslot_mem x).1; omega), if_pos (cslot_mem x).2]
  simp only [if_pos (cok x)]
  rw [cjA_c, cjB_c]

lemma eligOf_e' (e : EJob (ofInstance G)) :
    eligOf G (jobNum G (Sum.inr (Sum.inl e))) =
      [pairIdx (((ofInstance G).color e.1.1 : ℕ)) (((ofInstance G).color e.1.2 : ℕ))] := by
  rw [eligOf, if_neg (by have := (eslot_mem e).1; omega),
    if_neg (by have := (eslot_mem e).1; omega)]
  simp only [if_pos (eok e)]
  rw [ejU_e, ejV_e, col_vnum, col_vnum]

lemma elig_v_eq (x : VJob (ofInstance G)) :
    (isem (ofInstance G) (ord G)).elig (Sum.inl x) = vElig (ofInstance G) x := rfl

lemma elig_c_eq (x : CJob (ofInstance G)) :
    (isem (ofInstance G) (ord G)).elig (Sum.inr (Sum.inr x)) = {edgeMachine x.1.1} := rfl

lemma elig_e_eq (e : EJob (ofInstance G)) :
    (isem (ofInstance G) (ord G)).elig (Sum.inr (Sum.inl e)) =
      {edgeMachine (⟨((ofInstance G).color e.1.1, (ofInstance G).color e.1.2), e.2.1⟩ :
        ColorPair G.colours)} := rfl

/-- The eligible machines correspond, machine by machine. -/
lemma elig_mem_iff (j : Job (ofInstance G)) (m : Machine G.colours) :
    ((machFun G m : Fin (nMach G)) : ℕ) ∈ eligOf G (jobNum G j)
      ↔ m ∈ (isem (ofInstance G) (ord G)).elig j := by
  match j, m with
  | Sum.inl x, none =>
      have hmem : (none : Machine G.colours) ∈ vElig (ofInstance G) x :=
        validation_mem_vElig (ofInstance G) x
      by_cases h : x.2 = (ofInstance G).color x.1
      · rw [eligOf_v_own x h, elig_v_eq]
        simp only [machFun_none_val, List.mem_singleton, validation]
        exact ⟨fun _ => hmem, fun _ => trivial⟩
      · rw [eligOf_v_other x h, elig_v_eq]
        simp only [machFun_none_val, List.mem_cons, validation]
        exact ⟨fun _ => hmem, fun _ => Or.inl trivial⟩
  | Sum.inl x, some c =>
      refine Iff.trans ?_ (mem_vElig_edge (ofInstance G) x c).symm
      by_cases h : x.2 = (ofInstance G).color x.1
      · rw [eligOf_v_own x h]
        simp only [machFun_some_val, List.mem_singleton, validation]
        constructor
        · intro hc; exact absurd hc (pairIdx_ne_val c)
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact absurd (h1.symm.trans (h.symm.trans h2)) c.lo_ne_hi
          · exact absurd (h2.symm.trans (h.trans h1)) c.lo_ne_hi
      · rw [eligOf_v_other x h]
        have hne : (x.2 : ℕ) ≠ (((ofInstance G).color x.1 : ℕ)) := fun hc => h (Fin.ext hc)
        have hmm : min (x.2 : ℕ) (((ofInstance G).color x.1 : ℕ))
            < max (x.2 : ℕ) (((ofInstance G).color x.1 : ℕ)) := by omega
        have hlohi : (c.lo : ℕ) < (c.hi : ℕ) := c.lo_lt_hi
        simp only [machFun_some_val, List.mem_cons, List.not_mem_nil, or_false, validation]
        constructor
        · rintro (hc | hc)
          · exact absurd hc (pairIdx_ne_val c)
          · obtain ⟨h1, h2⟩ := pairIdx_inj (by exact c.lo_lt_hi) hmm hc
            rcases Nat.lt_or_ge (x.2 : ℕ) (((ofInstance G).color x.1 : ℕ)) with hlt | hge
            · exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
            · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · refine Or.inr ?_
            have e1 : (((ofInstance G).color x.1 : ℕ)) = (c.lo : ℕ) := congrArg Fin.val h1
            have e2 : (x.2 : ℕ) = (c.hi : ℕ) := congrArg Fin.val h2
            rw [show min (x.2 : ℕ) (((ofInstance G).color x.1 : ℕ)) = (c.lo : ℕ) by omega,
              show max (x.2 : ℕ) (((ofInstance G).color x.1 : ℕ)) = (c.hi : ℕ) by omega]
          · refine Or.inr ?_
            have e1 : (((ofInstance G).color x.1 : ℕ)) = (c.hi : ℕ) := congrArg Fin.val h1
            have e2 : (x.2 : ℕ) = (c.lo : ℕ) := congrArg Fin.val h2
            rw [show min (x.2 : ℕ) (((ofInstance G).color x.1 : ℕ)) = (c.lo : ℕ) by omega,
              show max (x.2 : ℕ) (((ofInstance G).color x.1 : ℕ)) = (c.hi : ℕ) by omega]
  | Sum.inr (Sum.inr x), none =>
      rw [eligOf_c' x]
      simp only [machFun_none_val, List.mem_singleton]
      constructor
      · intro hc; exact absurd hc.symm (pairIdx_ne_val x.1.1)
      · intro hc
        rw [elig_c_eq] at hc
        exact absurd (Finset.eq_of_mem_singleton hc) (by simp [edgeMachine])
  | Sum.inr (Sum.inr x), some c =>
      rw [eligOf_c' x]
      simp only [machFun_some_val, List.mem_singleton]
      rw [elig_c_eq]
      constructor
      · intro hc
        obtain ⟨h1, h2⟩ := pairIdx_inj (by exact c.lo_lt_hi) (by exact x.1.1.lo_lt_hi) hc
        rw [show (some c : Machine G.colours) = edgeMachine x.1.1 from
          congrArg edgeMachine (ColorPair.eq_of (Fin.ext h1) (Fin.ext h2))]
        exact Finset.mem_singleton_self _
      · intro hc
        rw [edgeMachine_inj (Finset.eq_of_mem_singleton hc)]
  | Sum.inr (Sum.inl e), none =>
      rw [eligOf_e' e]
      simp only [machFun_none_val, List.mem_singleton]
      constructor
      · intro hc
        exact absurd hc.symm (pairIdx_ne_val (⟨((ofInstance G).color e.1.1,
          (ofInstance G).color e.1.2), e.2.1⟩ : ColorPair G.colours))
      · intro hc
        rw [elig_e_eq] at hc
        exact absurd (Finset.eq_of_mem_singleton hc) (by simp [edgeMachine])
  | Sum.inr (Sum.inl e), some c =>
      rw [eligOf_e' e]
      simp only [machFun_some_val, List.mem_singleton]
      rw [elig_e_eq]
      constructor
      · intro hc
        obtain ⟨h1, h2⟩ := pairIdx_inj (by exact c.lo_lt_hi) (by exact e.2.1) hc
        rw [show (some c : Machine G.colours)
            = edgeMachine (⟨((ofInstance G).color e.1.1, (ofInstance G).color e.1.2), e.2.1⟩ :
              ColorPair G.colours) from
          congrArg edgeMachine (ColorPair.eq_of (Fin.ext h1) (Fin.ext h2))]
        exact Finset.mem_singleton_self _
      · intro hc
        rw [edgeMachine_inj (Finset.eq_of_mem_singleton hc)]
        rfl

lemma elig_eq_image (j : Job (ofInstance G)) :
    (inst G).eligible (jobFun G j)
      = ((isem (ofInstance G) (ord G)).elig j).image (machEquiv G) := by
  refine Finset.ext (fun (i : Fin (nMach G)) => ?_)
  show (i ∈ Finset.univ.filter (fun i : Fin (nMach G) => (i : ℕ) ∈ eligOf G (jobNum G j)))
    ↔ i ∈ ((isem (ofInstance G) (ord G)).elig j).image (machEquiv G)
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hi
    obtain ⟨m, hm⟩ := (machEquiv G).surjective i
    refine Finset.mem_image.mpr ⟨m, (elig_mem_iff j m).mp ?_, hm⟩
    rw [show (machFun G m : Fin (nMach G)) = i from (machEquiv_apply G m).symm.trans hm]
    exact hi
  · intro hi
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hi
    rw [← he, machEquiv_apply]
    exact (elig_mem_iff j m).mpr hm

/-! ### Every real slot is a job -/

lemma col_mk {u : ℕ} (hu : u < G.vertices) :
    col (G := G) u = ((G.colour ⟨u, hu⟩ : Fin G.colours) : ℕ) := dif_pos hu

lemma exists_job_v {s : ℕ} (hs : s < nVJob G) : ∃ j, jobNum G j = s := by
  have hk : 0 < G.colours := by
    by_contra hcon
    have hz : G.colours = 0 := by omega
    simp only [nVJob, hz, Nat.mul_zero] at hs
    omega
  have hl : s % G.colours < G.colours := Nat.mod_lt _ hk
  have hv : s / G.colours < G.vertices := by
    rw [Nat.div_lt_iff_lt_mul hk]
    exact hs
  refine ⟨Sum.inl (⟨s / G.colours, hv⟩, ⟨s % G.colours, hl⟩), ?_⟩
  show vIdx G (s / G.colours) (s % G.colours) = s
  simp only [vIdx]
  exact Nat.div_add_mod' s G.colours

lemma exists_job_c {s : ℕ} (h1 : nVJob G ≤ s) (h2 : s < nVJob G + nCJob G)
    (hok : CJobOk G (s - nVJob G)) : ∃ j, jobNum G j = s := by
  obtain ⟨hab, hbk, hz, hcol⟩ := hok
  have hak : cjA G (s - nVJob G) < G.colours := lt_trans hab hbk
  refine ⟨Sum.inr (Sum.inr ⟨(⟨(⟨cjA G (s - nVJob G), hak⟩, ⟨cjB G (s - nVJob G), hbk⟩), hab⟩,
    ⟨cjZ G (s - nVJob G), hz⟩), ?_⟩), ?_⟩
  · rcases hcol with hc | hc
    · exact Or.inl (Fin.ext ((col_mk hz).symm.trans hc))
    · exact Or.inr (Fin.ext ((col_mk hz).symm.trans hc))
  · show cIdx G (cjA G (s - nVJob G)) (cjB G (s - nVJob G)) (cjZ G (s - nVJob G)) = s
    simp only [cIdx, cjA, cjB, cjZ]
    have e1 : (s - nVJob G) / G.vertices / G.colours * G.colours
        + (s - nVJob G) / G.vertices % G.colours = (s - nVJob G) / G.vertices :=
      Nat.div_add_mod' _ _
    have e2 : (s - nVJob G) / G.vertices * G.vertices + (s - nVJob G) % G.vertices
        = s - nVJob G := Nat.div_add_mod' _ _
    rw [e1]
    omega

lemma exists_job_e {s : ℕ} (h1 : nVJob G + nCJob G ≤ s)
    (hok : EJobOk G (s - nVJob G - nCJob G)) : ∃ j, jobNum G j = s := by
  set q := s - nVJob G - nCJob G with hqdef
  have hq : q < (edgeList G).length := hok
  have hmem : (edgeList G)[q] ∈ edgeList G := List.getElem_mem hq
  obtain ⟨hlt, hadj⟩ := (mem_edgeList G _).mp hmem
  refine ⟨Sum.inr (Sum.inl ⟨((edgeList G)[q].1, (edgeList G)[q].2), hlt, hadj⟩), ?_⟩
  have hpe : epair G (⟨((edgeList G)[q].1, (edgeList G)[q].2), hlt, hadj⟩ :
      EJob (ofInstance G)) = (edgeList G)[q] := rfl
  have : eidx G (⟨((edgeList G)[q].1, (edgeList G)[q].2), hlt, hadj⟩ :
      EJob (ofInstance G)) = q := by
    rw [eidx, hpe]
    exact List.Nodup.idxOf_getElem (edgeList_nodup G) q hq
  rw [jobNum_e, eIdx, this]
  omega

lemma inert {s : Fin (nJobs G)} (hs : ∀ j, jobFun G j ≠ s) :
    eligOf G (s : ℕ) = [] ∧ wtOf G (s : ℕ) = 0 := by
  have hs' : ∀ j, jobNum G j ≠ (s : ℕ) := fun j h => hs j (Fin.ext h)
  rcases Nat.lt_or_ge (s : ℕ) (nVJob G) with h | h
  · obtain ⟨j, hj⟩ := exists_job_v h
    exact absurd hj (hs' j)
  · rcases Nat.lt_or_ge (s : ℕ) (nVJob G + nCJob G) with h2 | h2
    · by_cases hok : CJobOk G ((s : ℕ) - nVJob G)
      · obtain ⟨j, hj⟩ := exists_job_c h h2 hok
        exact absurd hj (hs' j)
      · refine ⟨Lax470956Proofs.Construction1Slots.eligOf_cIdx_inert h h2 hok, ?_⟩
        rw [wtOf, if_neg (by omega), if_pos h2]
        simp only [if_neg hok]
    · by_cases hok : EJobOk G ((s : ℕ) - nVJob G - nCJob G)
      · obtain ⟨j, hj⟩ := exists_job_e h2 hok
        exact absurd hj (hs' j)
      · refine ⟨Lax470956Proofs.Construction1Slots.eligOf_eIdx_inert (by omega) hok, ?_⟩
        rw [wtOf, if_neg (by omega), if_neg (by omega)]
        simp only [if_neg hok]

/-! ### The renumbering, and Construction 1's correctness -/

variable (G)

/-- **Construction 1's two presentations are the same instance, renumbered and padded.** -/
noncomputable def renum :
    Lax470956Proofs.Renumber.Renumbering (isem (ofInstance G) (ord G)) (inst G) where
  job := jobFun G
  job_inj := jobFun_inj
  mach := machEquiv G
  p_eq := procOf_eq
  d_eq := dueOf_eq
  w_eq := wt_eq
  elig_eq := elig_eq_image
  inert_elig := fun s hs => by
    refine Finset.ext (fun (i : Fin (nMach G)) => ?_)
    show (i ∈ Finset.univ.filter (fun i : Fin (nMach G) => (i : ℕ) ∈ eligOf G (s : ℕ)))
      ↔ i ∈ (∅ : Finset (Fin (nMach G)))
    rw [Finset.mem_filter, (inert (fun j => hs j)).1]
    simp

/-- The two presentations admit feasible schedules of exactly the same weights. -/
theorem hasWeight_iff (W : ℕ) :
    (isem (ofInstance G) (ord G)).HasWeight W ↔ (inst G).HasWeight W :=
  Lax470956Proofs.Renumber.Renumbering.hasWeight_iff (renum G) W

/--
---
conclusion: Lax470956.Construction1.correct
---
Section 3 of the paper, joined to the archive's shapes.

The argument itself — Observation 3, Lemma 1 and Lemma 2 — is the paper's, proved over
the paper's own presentation: an abstract finite vertex type, and jobs and machines named
structurally as sums and subtypes. Three translations carry it to the numbered instance
the concept builds. `ofInstance` is the instance shape, and on it the two notions of
multicoloured clique are the same proposition. `ord` is the order `<π`, which
the paper assumes exists and the concept fixes by ranking vertices by colour and breaking
ties by index. And `renum` is the numbering: the machines correspond exactly, the jobs
embed, and the slots outside that embedding carry inert jobs — weight zero and no
eligible machine at all, so feasibility alone forces a schedule to reject them and they
change neither side.

The padding is the cost of indexing by all ordered pairs. A closed-form job index is two
divisions, where enumerating only the edges of the graph would be a search; the cost is
`n²` edge slots of which only the edges are jobs, and `Renumbering.hasWeight_iff` is
where it is paid.
-/
theorem correct (G : Lax470956.MulticolouredClique.Instance) :
    G.HasMulticolouredClique ↔ (inst G).HasWeight (targetWeight G) :=
  correct_of_renumbering G (hasWeight_iff G)

end Lax470956Proofs.Construction1Renum
