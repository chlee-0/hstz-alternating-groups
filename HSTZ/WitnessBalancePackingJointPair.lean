import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalancePackingGrouping

/-! The ordered pair of joint factors, and the grouping with the rest.
Reuses OpenAI's `math` repository (commit adc7f1241, Apache-2.0) and Mathlib's
`PiTensorProduct` API. The original independent group actions are kept. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessBalancePackingJointPairSpace :=
  (witnessBalanceLocalProjectedFactor hk z 0).toSubmodule ⊗[ℂ]
    (witnessBalanceLocalProjectedFactor hk z (witnessBalancePackingJointLabel delta)).toSubmodule

/-- Ordered labels 0 and 1/2, via two explicit `Unit` indices. -/
def witnessBalancePackingJointPair : witnessBalancePackingJointTensorSpace hk z ≃ₗ[ℂ]
    witnessBalancePackingJointPairSpace hk z :=
  (PiTensorProduct.reindex ℂ
    (fun a : witnessBalancePackingJointIndex k delta =>
      (witnessBalanceLocalProjectedFactor hk z a.val.val).toSubmodule)
    (witnessBalancePackingJointOrder k delta).symm).trans
      ((PiTensorProduct.tmulEquivDep ℂ
        (fun u : Unit ⊕ Unit => (witnessBalanceLocalProjectedFactor hk z
          (witnessBalancePackingJointOrder k delta u).val.val).toSubmodule)).symm.trans
        (TensorProduct.congr (PiTensorProduct.subsingletonEquiv ())
          (PiTensorProduct.subsingletonEquiv ())))

theorem witnessBalancePackingJointPair_tprod
    (x : ∀ a : witnessBalancePackingJointIndex k delta,
      (witnessBalanceLocalProjectedFactor hk z a.val.val).toSubmodule) :
    witnessBalancePackingJointPair hk z (PiTensorProduct.tprod ℂ x)=
      x (witnessBalancePackingJointOrder k delta (.inl ())) ⊗ₜ[ℂ]
        x (witnessBalancePackingJointOrder k delta (.inr ())) := by
  let N : Unit ⊕ Unit → Type := fun u : Unit ⊕ Unit => (witnessBalanceLocalProjectedFactor hk z
    (witnessBalancePackingJointOrder k delta u).val.val).toSubmodule
  let L := PiTensorProduct.subsingletonEquiv (R:=ℂ) (s:=fun u : Unit => N (.inl u)) ()
  let R := PiTensorProduct.subsingletonEquiv (R:=ℂ) (s:=fun u : Unit => N (.inr u)) ()
  change TensorProduct.congr L R ((PiTensorProduct.tmulEquivDep ℂ N).symm
    (PiTensorProduct.reindex ℂ
      (fun a : witnessBalancePackingJointIndex k delta =>
        (witnessBalanceLocalProjectedFactor hk z a.val.val).toSubmodule)
      (witnessBalancePackingJointOrder k delta).symm (PiTensorProduct.tprod ℂ x)))=_
  erw [PiTensorProduct.reindex_tprod]
  simp only [Equiv.symm_symm]
  have he := PiTensorProduct.tmulEquivDep_symm_apply ℂ N
    (fun u => x (witnessBalancePackingJointOrder k delta u))
  erw [he,TensorProduct.congr_tmul]
  erw [PiTensorProduct.subsingletonEquiv_apply_tprod,PiTensorProduct.subsingletonEquiv_apply_tprod]

abbrev witnessBalancePackingJointPairRestSpace :=
  witnessBalancePackingJointPairSpace hk z ⊗[ℂ] witnessBalancePackingRestTensorSpace hk z

def witnessBalancePackingJointPairGrouping : witnessBalancePackingTensorSpace hk z ≃ₗ[ℂ]
    witnessBalancePackingJointPairRestSpace hk z :=
  (witnessBalancePackingGrouping hk z).trans
    (TensorProduct.congr (witnessBalancePackingJointPair hk z)
      (LinearEquiv.refl ℂ (witnessBalancePackingRestTensorSpace hk z)))

theorem witnessBalancePackingJointPairGrouping_tprod
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule) :
    witnessBalancePackingJointPairGrouping hk z (PiTensorProduct.tprod ℂ x)=
      (x (witnessBalancePackingJointOrder k delta (.inl ())).val ⊗ₜ[ℂ]
        x (witnessBalancePackingJointOrder k delta (.inr ())).val) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun a : witnessBalancePackingRestIndex k delta => x a.val) := by
  erw [witnessBalancePackingJointPairGrouping,LinearEquiv.trans_apply,
    witnessBalancePackingGrouping_tprod,TensorProduct.congr_tmul,
    witnessBalancePackingJointPair_tprod]
  rfl

/-- Restrict the product over all labels to the two original joint component groups. -/
def witnessBalancePackingJointProductHom : witnessBalancePackingOriginalGroup hk z →*
    (Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0)) ×
      Equiv.Perm (Fin (witnessBalanceComponentSize hk z (witnessBalancePackingJointLabel delta)))) where
  toFun g := (g (witnessBalancePackingJointOrder k delta (.inl ())).val,
    g (witnessBalancePackingJointOrder k delta (.inr ())).val)
  map_one' := rfl
  map_mul' _ _ := rfl

def witnessBalancePackingJointPairAction : Representation ℂ
    (witnessBalancePackingOriginalGroup hk z) (witnessBalancePackingJointPairSpace hk z) :=
  (independentTensor (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation
    (witnessBalanceLocalProjectedFactor hk z (witnessBalancePackingJointLabel delta)).toRepresentation).comp
      (witnessBalancePackingJointProductHom hk z)

def witnessBalancePackingJointPairRestAction : Representation ℂ
    (witnessBalancePackingOriginalGroup hk z) (witnessBalancePackingJointPairRestSpace hk z) :=
  Representation.tprod (witnessBalancePackingJointPairAction hk z)
    (witnessBalancePackingRestTensorAction hk z)

/-- Intertwining regrouping into F0 ⊗ (F1 or F2) and all remaining factors. -/
def witnessBalancePackingJointPairGroupingMap : Representation.IntertwiningMap
    (witnessBalancePackingTensorAction hk z) (witnessBalancePackingJointPairRestAction hk z) where
  toLinearMap := (witnessBalancePackingJointPairGrouping hk z).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    have he : (witnessBalancePackingJointPairGrouping hk z).toLinearMap.comp
        (witnessBalancePackingTensorAction hk z g)=
      (witnessBalancePackingJointPairRestAction hk z g).comp
        (witnessBalancePackingJointPairGrouping hk z).toLinearMap := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      change witnessBalancePackingJointPairGrouping hk z
        (witnessBalancePackingTensorAction hk z g (PiTensorProduct.tprod ℂ x))=_
      rw [witnessBalancePackingTensorAction_tprod,witnessBalancePackingJointPairGrouping_tprod]
      change _=TensorProduct.map (witnessBalancePackingJointPairAction hk z g)
        (witnessBalancePackingRestTensorAction hk z g)
        (witnessBalancePackingJointPairGrouping hk z (PiTensorProduct.tprod ℂ x))
      rw [witnessBalancePackingJointPairGrouping_tprod hk z x]
      change _ =
        witnessBalancePackingJointPairAction hk z g
          (x (witnessBalancePackingJointOrder k delta (.inl ())).val ⊗ₜ[ℂ]
            x (witnessBalancePackingJointOrder k delta (.inr ())).val) ⊗ₜ[ℂ]
          witnessBalancePackingRestTensorAction hk z g
            (PiTensorProduct.tprod ℂ (fun a : witnessBalancePackingRestIndex k delta => x a.val))
      change _= (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation
          (g (witnessBalancePackingJointOrder k delta (.inl ())).val)
          (x (witnessBalancePackingJointOrder k delta (.inl ())).val) ⊗ₜ[ℂ]
        (witnessBalanceLocalProjectedFactor hk z (witnessBalancePackingJointLabel delta)).toRepresentation
          (g (witnessBalancePackingJointOrder k delta (.inr ())).val)
          (x (witnessBalancePackingJointOrder k delta (.inr ())).val) ⊗ₜ[ℂ]
        PiTensorProduct.map (fun a : witnessBalancePackingRestIndex k delta =>
          witnessBalancePackingFactorAction hk z a.val g)
          (PiTensorProduct.tprod ℂ (fun a => x a.val))
      rw [PiTensorProduct.map_tprod]
      rfl
    exact DFunLike.congr_fun he q

theorem witnessBalancePackingJointPairGroupingMap_bijective :
    Function.Bijective (witnessBalancePackingJointPairGroupingMap hk z) :=
  (witnessBalancePackingJointPairGrouping hk z).bijective

/-- The original group H acting on the pair and the remaining factors. -/
def witnessBalancePackingJointPairRestHAction (hd : delta≤1) : Representation ℂ
    (witnessBalanceGroup hk z) (witnessBalancePackingJointPairRestSpace hk z) :=
  (witnessBalancePackingJointPairRestAction hk z).comp
    (witnessBalancePackingOriginalEquiv hk z hd).symm.toMonoidHom

def witnessBalancePackingJointPairGroupingHMap (hd : delta≤1) : Representation.IntertwiningMap
    (witnessBalancePackingTensorHAction hk z hd)
    (witnessBalancePackingJointPairRestHAction hk z hd) where
  toLinearMap := (witnessBalancePackingJointPairGrouping hk z).toLinearMap
  isIntertwining' g := LinearMap.ext fun q => (witnessBalancePackingJointPairGroupingMap hk z).map_action
    ((witnessBalancePackingOriginalEquiv hk z hd).symm g) q

theorem witnessBalancePackingJointPairGroupingHMap_bijective (hd : delta≤1) :
    Function.Bijective (witnessBalancePackingJointPairGroupingHMap hk z hd) :=
  (witnessBalancePackingJointPairGrouping hk z).bijective

private def pairInverseHMap (hd : delta≤1) : Representation.IntertwiningMap
    (witnessBalancePackingJointPairRestHAction hk z hd)
    (witnessBalancePackingTensorHAction hk z hd) where
  toLinearMap := (witnessBalancePackingJointPairGrouping hk z).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    apply (witnessBalancePackingJointPairGrouping hk z).injective
    change witnessBalancePackingJointPairGrouping hk z
      ((witnessBalancePackingJointPairGrouping hk z).symm
        (witnessBalancePackingJointPairRestHAction hk z hd g q))=
      witnessBalancePackingJointPairGrouping hk z
        (witnessBalancePackingTensorHAction hk z hd g
          ((witnessBalancePackingJointPairGrouping hk z).symm q))
    rw [LinearEquiv.apply_symm_apply]
    have he := (witnessBalancePackingJointPairGroupingHMap hk z hd).map_action g
      ((witnessBalancePackingJointPairGrouping hk z).symm q)
    change witnessBalancePackingJointPairGrouping hk z
        (witnessBalancePackingTensorHAction hk z hd g
          ((witnessBalancePackingJointPairGrouping hk z).symm q))=
      witnessBalancePackingJointPairRestHAction hk z hd g
        (witnessBalancePackingJointPairGrouping hk z
          ((witnessBalancePackingJointPairGrouping hk z).symm q)) at he
    rw [LinearEquiv.apply_symm_apply] at he
    exact he.symm

/-- Paired-word map at the pair positions, using the same label cut. -/
def witnessBalancePackingJointPairWords (hd : delta≤1) :
    witnessBalancePackingJointPairRestSpace hk z →ₗ[ℂ] WordSpace n (witnessBalancePairDim k b delta hk) :=
  (witnessBalancePackingTensorWords hk z hd).comp
    (witnessBalancePackingJointPairGrouping hk z).symm.toLinearMap

theorem witnessBalancePackingJointPairWords_tprod (hd : delta≤1)
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    witnessBalancePackingJointPairWords hk z hd
      ((x (witnessBalancePackingJointOrder k delta (.inl ())).val ⊗ₜ[ℂ]
        x (witnessBalancePackingJointOrder k delta (.inr ())).val) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun a : witnessBalancePackingRestIndex k delta => x a.val)) w=
      ∏ a, (x a).val (witnessBalancePackingPairRestriction hk z hd w a) := by
  erw [← witnessBalancePackingJointPairGrouping_tprod,witnessBalancePackingJointPairWords,LinearMap.comp_apply]
  change witnessBalancePackingTensorWords hk z hd
    ((witnessBalancePackingJointPairGrouping hk z).symm
      (witnessBalancePackingJointPairGrouping hk z (PiTensorProduct.tprod ℂ x))) w=_
  rw [LinearEquiv.symm_apply_apply,witnessBalancePackingTensorWords_tprod]

theorem witnessBalancePackingJointPairWords_range (hd : delta≤1) :
    (witnessBalancePackingJointPairWords hk z hd).range=
      (witnessBalanceProjectedRange hk z
        (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
        (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toSubmodule := by
  rw [witnessBalancePackingJointPairWords,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (witnessBalancePackingJointPairGrouping hk z).symm.surjective,
    Submodule.map_top]
  exact witnessBalancePackingTensorImage_eq_original hk z hd

/-- Map from the pair and the rest into the original range of `P J`, for the same H. -/
def witnessBalancePackingJointPairProjectedMap (hd : delta≤1) : Representation.IntertwiningMap
    (witnessBalancePackingJointPairRestHAction hk z hd)
    (witnessBalanceProjectedRange hk z
      (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toRepresentation :=
  (witnessBalancePackingTensorProjectedMap hk z hd).comp (pairInverseHMap hk z hd)

theorem witnessBalancePackingJointPairProjectedMap_bijective (hd : delta≤1) :
    Function.Bijective (witnessBalancePackingJointPairProjectedMap hk z hd) :=
  (witnessBalancePackingTensorProjectedMap_bijective hk z hd).comp
    (witnessBalancePackingJointPairGrouping hk z).symm.bijective

theorem witnessBalancePackingJointPairProjectedMap_physical (hd : delta≤1)
    (q : witnessBalancePackingJointPairRestSpace hk z) :
    (witnessBalancePackingJointPairProjectedMap hk z hd q).val=
      witnessBalancePackingJointPairWords hk z hd q := rfl

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingJointPair
#print axioms HSTZ.witnessBalancePackingJointPair_tprod
#print axioms HSTZ.witnessBalancePackingJointPairGrouping
#print axioms HSTZ.witnessBalancePackingJointPairGrouping_tprod
#print axioms HSTZ.witnessBalancePackingJointProductHom
#print axioms HSTZ.witnessBalancePackingJointPairAction
#print axioms HSTZ.witnessBalancePackingJointPairRestAction
#print axioms HSTZ.witnessBalancePackingJointPairGroupingMap
#print axioms HSTZ.witnessBalancePackingJointPairGroupingMap_bijective

#print axioms HSTZ.witnessBalancePackingJointPairRestHAction
#print axioms HSTZ.witnessBalancePackingJointPairGroupingHMap
#print axioms HSTZ.witnessBalancePackingJointPairGroupingHMap_bijective
#print axioms HSTZ.witnessBalancePackingJointPairWords
#print axioms HSTZ.witnessBalancePackingJointPairWords_tprod
#print axioms HSTZ.witnessBalancePackingJointPairWords_range
#print axioms HSTZ.witnessBalancePackingJointPairProjectedMap
#print axioms HSTZ.witnessBalancePackingJointPairProjectedMap_bijective
#print axioms HSTZ.witnessBalancePackingJointPairProjectedMap_physical
