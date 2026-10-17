import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalancePackingImage

/-! Grouping of the tensor over all original labels into the joint labels and the rest.
Reuses OpenAI's `math` repository (commit adc7f1241, Apache-2.0) and Mathlib's
`PiTensorProduct`/`Equiv` API. This file only regroups tensor factors; it proves no
Young support. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct

def witnessBalancePackingJointLabel (delta : ℕ) : ℕ := if delta=0 then 1 else 2

def witnessBalancePackingJointPredicate (k delta : ℕ)
    (a : witnessBalancePackingLabelIndex k delta) : Prop :=
  a.val=0 ∨ a.val=witnessBalancePackingJointLabel delta

abbrev witnessBalancePackingJointIndex (k delta : ℕ) :=
  {a : witnessBalancePackingLabelIndex k delta // witnessBalancePackingJointPredicate k delta a}
abbrev witnessBalancePackingRestIndex (k delta : ℕ) :=
  {a : witnessBalancePackingLabelIndex k delta // ¬witnessBalancePackingJointPredicate k delta a}

/-- Cut the labels into the joint labels and the rest, which consists of all
original labels outside the joint set. -/
def witnessBalancePackingJointRestCut (k delta : ℕ) : witnessBalancePackingLabelIndex k delta ≃
    witnessBalancePackingJointIndex k delta ⊕ witnessBalancePackingRestIndex k delta :=
  (Equiv.sumCompl (witnessBalancePackingJointPredicate k delta)).symm

theorem witnessBalancePackingJointRestCut_left (k delta : ℕ)
    (a : witnessBalancePackingJointIndex k delta) :
    (witnessBalancePackingJointRestCut k delta).symm (.inl a)=a.val := rfl

theorem witnessBalancePackingJointRestCut_right (k delta : ℕ)
    (a : witnessBalancePackingRestIndex k delta) :
    (witnessBalancePackingJointRestCut k delta).symm (.inr a)=a.val := rfl

private theorem jointLabel_mem (k delta a : ℕ)
    (ha : a=0 ∨ a=witnessBalancePackingJointLabel delta) :
    a∈witnessBalancePackingOriginalLabels k delta := by
  apply List.mem_flatMap.mpr
  refine ⟨.joint,?_,?_⟩
  · simp [witnessBalancePackingBlocks]
  · simpa [witnessBalancePackingLabels,witnessBalancePackingJointLabel] using ha

private def jointZero (k delta : ℕ) : witnessBalancePackingJointIndex k delta :=
  ⟨⟨0,jointLabel_mem k delta 0 (Or.inl rfl)⟩,Or.inl rfl⟩
private def jointSecond (k delta : ℕ) : witnessBalancePackingJointIndex k delta :=
  ⟨⟨witnessBalancePackingJointLabel delta,jointLabel_mem k delta _ (Or.inr rfl)⟩,Or.inr rfl⟩
private theorem jointSecond_ne_zero (delta : ℕ) : witnessBalancePackingJointLabel delta≠0 := by
  by_cases hd : delta=0 <;> simp [witnessBalancePackingJointLabel,hd]

/-- The ordered joint labels: first 0, then 1 (if delta = 0) or 2 (if delta = 1). -/
def witnessBalancePackingJointOrder (k delta : ℕ) : Unit ⊕ Unit ≃
    witnessBalancePackingJointIndex k delta where
  toFun u := match u with | .inl _ => jointZero k delta | .inr _ => jointSecond k delta
  invFun a := if a.val.val=0 then .inl () else .inr ()
  left_inv u := by
    rcases u with ⟨⟩ | ⟨⟩
    · simp [jointZero]
    · simp [jointSecond,jointSecond_ne_zero]
  right_inv a := by
    by_cases h : a.val.val=0
    · simp only [if_pos h]
      apply Subtype.ext
      apply Subtype.ext
      exact h.symm
    · simp only [if_neg h]
      apply Subtype.ext
      apply Subtype.ext
      exact (a.property.resolve_left h).symm

theorem witnessBalancePackingJointOrder_first (k delta : ℕ) :
    (witnessBalancePackingJointOrder k delta (.inl ())).val.val=0 := rfl

theorem witnessBalancePackingJointOrder_second (k delta : ℕ) :
    (witnessBalancePackingJointOrder k delta (.inr ())).val.val=
      witnessBalancePackingJointLabel delta := rfl

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessBalancePackingJointTensorSpace :=
  ⨂[ℂ] a : witnessBalancePackingJointIndex k delta,
    (witnessBalanceLocalProjectedFactor hk z a.val.val).toSubmodule
abbrev witnessBalancePackingRestTensorSpace :=
  ⨂[ℂ] a : witnessBalancePackingRestIndex k delta,
    (witnessBalanceLocalProjectedFactor hk z a.val.val).toSubmodule
abbrev witnessBalancePackingGroupedTensorSpace :=
  witnessBalancePackingJointTensorSpace hk z ⊗[ℂ] witnessBalancePackingRestTensorSpace hk z

/-- Finite reindexing, followed by the sum-index tensor equivalence. -/
def witnessBalancePackingGrouping : witnessBalancePackingTensorSpace hk z ≃ₗ[ℂ]
    witnessBalancePackingGroupedTensorSpace hk z :=
  (PiTensorProduct.reindex ℂ
    (fun a : witnessBalancePackingLabelIndex k delta =>
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule)
    (witnessBalancePackingJointRestCut k delta)).trans
      (PiTensorProduct.tmulEquivDep ℂ
        (fun a : witnessBalancePackingJointIndex k delta ⊕ witnessBalancePackingRestIndex k delta =>
          (witnessBalanceLocalProjectedFactor hk z
            ((witnessBalancePackingJointRestCut k delta).symm a).val).toSubmodule)).symm

theorem witnessBalancePackingGrouping_tprod
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule) :
    witnessBalancePackingGrouping hk z (PiTensorProduct.tprod ℂ x)=
      PiTensorProduct.tprod ℂ (fun a : witnessBalancePackingJointIndex k delta => x a.val) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun a : witnessBalancePackingRestIndex k delta => x a.val) := by
  erw [witnessBalancePackingGrouping,LinearEquiv.trans_apply,PiTensorProduct.reindex_tprod]
  exact PiTensorProduct.tmulEquivDep_symm_apply ℂ
    (fun a : witnessBalancePackingJointIndex k delta ⊕ witnessBalancePackingRestIndex k delta =>
      (witnessBalanceLocalProjectedFactor hk z
        ((witnessBalancePackingJointRestCut k delta).symm a).val).toSubmodule)
    (fun i => x ((witnessBalancePackingJointRestCut k delta).symm i))

def witnessBalancePackingJointTensorAction : Representation ℂ
    (witnessBalancePackingOriginalGroup hk z) (witnessBalancePackingJointTensorSpace hk z) where
  toFun g := PiTensorProduct.map fun a => witnessBalancePackingFactorAction hk z a.val g
  map_one' := by simp only [map_one]; exact PiTensorProduct.map_one
  map_mul' g h := by simp only [map_mul]; exact PiTensorProduct.map_mul _ _

def witnessBalancePackingRestTensorAction : Representation ℂ
    (witnessBalancePackingOriginalGroup hk z) (witnessBalancePackingRestTensorSpace hk z) where
  toFun g := PiTensorProduct.map fun a => witnessBalancePackingFactorAction hk z a.val g
  map_one' := by simp only [map_one]; exact PiTensorProduct.map_one
  map_mul' g h := by simp only [map_mul]; exact PiTensorProduct.map_mul _ _

/-- The group on all labels acts through its restrictions to the joint labels and to the rest. -/
def witnessBalancePackingGroupedTensorAction : Representation ℂ
    (witnessBalancePackingOriginalGroup hk z) (witnessBalancePackingGroupedTensorSpace hk z) :=
  Representation.tprod (witnessBalancePackingJointTensorAction hk z)
    (witnessBalancePackingRestTensorAction hk z)

/-- Equivariance of the grouping map, proved for all vectors. -/
def witnessBalancePackingGroupingMap : Representation.IntertwiningMap
    (witnessBalancePackingTensorAction hk z) (witnessBalancePackingGroupedTensorAction hk z) where
  toLinearMap := (witnessBalancePackingGrouping hk z).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    have he : (witnessBalancePackingGrouping hk z).toLinearMap.comp
        (witnessBalancePackingTensorAction hk z g)=
      (witnessBalancePackingGroupedTensorAction hk z g).comp
        (witnessBalancePackingGrouping hk z).toLinearMap := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      change witnessBalancePackingGrouping hk z
        (witnessBalancePackingTensorAction hk z g (PiTensorProduct.tprod ℂ x))=_
      rw [witnessBalancePackingTensorAction_tprod,witnessBalancePackingGrouping_tprod]
      change _=TensorProduct.map (witnessBalancePackingJointTensorAction hk z g)
        (witnessBalancePackingRestTensorAction hk z g)
        (witnessBalancePackingGrouping hk z (PiTensorProduct.tprod ℂ x))
      rw [witnessBalancePackingGrouping_tprod,TensorProduct.map_tmul]
      change _=PiTensorProduct.map (fun a : witnessBalancePackingJointIndex k delta =>
          witnessBalancePackingFactorAction hk z a.val g)
        (PiTensorProduct.tprod ℂ (fun a => x a.val)) ⊗ₜ[ℂ]
        PiTensorProduct.map (fun a : witnessBalancePackingRestIndex k delta =>
          witnessBalancePackingFactorAction hk z a.val g)
        (PiTensorProduct.tprod ℂ (fun a => x a.val))
      rw [PiTensorProduct.map_tprod,PiTensorProduct.map_tprod]
    exact DFunLike.congr_fun he q

theorem witnessBalancePackingGroupingMap_bijective :
    Function.Bijective (witnessBalancePackingGroupingMap hk z) :=
  (witnessBalancePackingGrouping hk z).bijective

/-- The original group H acting on the grouped tensor; the joint and rest actions
are restrictions of the label actions. -/
def witnessBalancePackingGroupedTensorHAction (hd : delta≤1) : Representation ℂ
    (witnessBalanceGroup hk z) (witnessBalancePackingGroupedTensorSpace hk z) :=
  (witnessBalancePackingGroupedTensorAction hk z).comp
    (witnessBalancePackingOriginalEquiv hk z hd).symm.toMonoidHom

def witnessBalancePackingGroupingHMap (hd : delta≤1) : Representation.IntertwiningMap
    (witnessBalancePackingTensorHAction hk z hd)
    (witnessBalancePackingGroupedTensorHAction hk z hd) where
  toLinearMap := (witnessBalancePackingGrouping hk z).toLinearMap
  isIntertwining' g := LinearMap.ext fun q => (witnessBalancePackingGroupingMap hk z).map_action
    ((witnessBalancePackingOriginalEquiv hk z hd).symm g) q

theorem witnessBalancePackingGroupingHMap_bijective (hd : delta≤1) :
    Function.Bijective (witnessBalancePackingGroupingHMap hk z hd) :=
  (witnessBalancePackingGrouping hk z).bijective

/-- Reassembly of the joint tensor and the rest into paired words. -/
def witnessBalancePackingGroupedWords (hd : delta≤1) :
    witnessBalancePackingGroupedTensorSpace hk z →ₗ[ℂ] WordSpace n (witnessBalancePairDim k b delta hk) :=
  (witnessBalancePackingTensorWords hk z hd).comp (witnessBalancePackingGrouping hk z).symm.toLinearMap

theorem witnessBalancePackingGroupedWords_tprod (hd : delta≤1)
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    witnessBalancePackingGroupedWords hk z hd
      (PiTensorProduct.tprod ℂ (fun a : witnessBalancePackingJointIndex k delta => x a.val) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun a : witnessBalancePackingRestIndex k delta => x a.val)) w=
      ∏ a, (x a).val (witnessBalancePackingPairRestriction hk z hd w a) := by
  rw [← witnessBalancePackingGrouping_tprod,witnessBalancePackingGroupedWords,LinearMap.comp_apply]
  change witnessBalancePackingTensorWords hk z hd
    ((witnessBalancePackingGrouping hk z).symm
      (witnessBalancePackingGrouping hk z (PiTensorProduct.tprod ℂ x))) w=_
  rw [LinearEquiv.symm_apply_apply,witnessBalancePackingTensorWords_tprod]

theorem witnessBalancePackingGroupedWords_range (hd : delta≤1) :
    (witnessBalancePackingGroupedWords hk z hd).range=
      (witnessBalanceProjectedRange hk z
        (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
        (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toSubmodule := by
  rw [witnessBalancePackingGroupedWords,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (witnessBalancePackingGrouping hk z).symm.surjective,
    Submodule.map_top]
  exact witnessBalancePackingTensorImage_eq_original hk z hd

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingJointRestCut
#print axioms HSTZ.witnessBalancePackingJointRestCut_left
#print axioms HSTZ.witnessBalancePackingJointRestCut_right
#print axioms HSTZ.witnessBalancePackingJointOrder
#print axioms HSTZ.witnessBalancePackingJointOrder_first
#print axioms HSTZ.witnessBalancePackingJointOrder_second
#print axioms HSTZ.witnessBalancePackingGrouping
#print axioms HSTZ.witnessBalancePackingGrouping_tprod
#print axioms HSTZ.witnessBalancePackingJointTensorAction
#print axioms HSTZ.witnessBalancePackingRestTensorAction
#print axioms HSTZ.witnessBalancePackingGroupedTensorAction
#print axioms HSTZ.witnessBalancePackingGroupingMap
#print axioms HSTZ.witnessBalancePackingGroupingMap_bijective

#print axioms HSTZ.witnessBalancePackingGroupedTensorHAction
#print axioms HSTZ.witnessBalancePackingGroupingHMap
#print axioms HSTZ.witnessBalancePackingGroupingHMap_bijective
#print axioms HSTZ.witnessBalancePackingGroupedWords
#print axioms HSTZ.witnessBalancePackingGroupedWords_tprod
#print axioms HSTZ.witnessBalancePackingGroupedWords_range
