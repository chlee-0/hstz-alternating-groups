import HSTZ.WitnessBalancePackingTensor

/-! The independent square and projector over all original labels.
Reuses `cyclicTensorInclusion`, `wordTensor`, the local projected map and Mathlib's
`PiTensorProduct` API, building on OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
No identification with the global square of `C` or target support is asserted. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
  (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessBalancePackingSquareSpace :=
  ⨂[ℂ] a : witnessBalancePackingLabelIndex k delta,
    ((witnessBalanceComponentRows hk z a.val).toSubmodule ⊗[ℂ]
      (witnessBalanceComponentRows hk z a.val).toSubmodule)

private def squareWords (a : witnessBalancePackingLabelIndex k delta) :=
  (wordTensor (witnessBalanceComponentSize hk z a.val)
    ((witnessDiagram k b delta hk).colLen 0) ((witnessDiagram k b delta hk).colLen 0)).toLinearMap.comp
      (cyclicTensorInclusion (wordRep _ _) (wordRep _ _)
        (witnessBalanceComponentWord hk z a.val) (witnessBalanceComponentWord hk z a.val)).toLinearMap

private def squareQuotient (a : witnessBalancePackingLabelIndex k delta) :
    ((witnessBalanceComponentRows hk z a.val).toSubmodule ⊗[ℂ]
      (witnessBalanceComponentRows hk z a.val).toSubmodule) →ₗ[ℂ]
        (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule :=
  (witnessBalanceLocalProjectedMap hk z a.val).toLinearMap.rangeRestrict

private theorem squareQuotient_value (a : witnessBalancePackingLabelIndex k delta) q :
    (squareQuotient hk z a q).val=
      coordinateProjection (witnessBalanceLocalPairWords hk z a.val) (squareWords hk z a q) := rfl

private theorem squareQuotient_surjective :
    Function.Surjective (PiTensorProduct.map (squareQuotient hk z)) := by
  apply LinearMap.range_eq_top.mp
  apply le_antisymm le_top
  rw [← PiTensorProduct.span_tprod_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  have h : ∀ a : witnessBalancePackingLabelIndex k delta,
      ∃ q, squareQuotient hk z a q=x a := fun a =>
    (witnessBalanceLocalProjectedMap hk z a.val).toLinearMap.surjective_rangeRestrict (x a)
  choose q hq using h
  refine ⟨PiTensorProduct.tprod ℂ q,?_⟩
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext a
  exact hq a

/-- The finite product of all full local squares; both layers are independent. -/
def witnessBalancePackingSquareWords (hd : delta ≤ 1) :
    witnessBalancePackingSquareSpace hk z →ₗ[ℂ]
      WordSpace n (witnessBalancePairDim k b delta hk) :=
  (witnessBalancePackingPositionTensor hk z hd).toLinearMap.comp
    (PiTensorProduct.map (squareWords hk z))

def witnessBalancePackingProjectedSquareWords (hd : delta ≤ 1) :
    witnessBalancePackingSquareSpace hk z →ₗ[ℂ]
      WordSpace n (witnessBalancePairDim k b delta hk) :=
  (witnessBalancePackingTensorWords hk z hd).comp
    (PiTensorProduct.map (squareQuotient hk z))

/-- The image of the finite independent local squares, which is distinct from
the global `range (P J)`. -/
theorem witnessBalancePackingProjectedSquareWords_range (hd : delta ≤ 1) :
    (witnessBalancePackingProjectedSquareWords hk z hd).range=
      (witnessBalancePackingTensorWords hk z hd).range := by
  rw [witnessBalancePackingProjectedSquareWords,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (squareQuotient_surjective hk z),Submodule.map_top]

/-- The global paired-word selector acts factorwise on every independent
local-square tensor. Stability of the unfiltered global square of `C` does not
follow. -/
theorem witnessBalancePackingSquareWords_projection (hd : delta ≤ 1)
    (q : witnessBalancePackingSquareSpace hk z) :
    coordinateProjection (witnessBalanceComponentWords hk z
      (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk))
        (witnessBalancePackingSquareWords hk z hd q)=
      witnessBalancePackingProjectedSquareWords hk z hd q := by
  rw [witnessBalancePackingSquareWords,LinearMap.comp_apply]
  change coordinateProjection (witnessBalanceComponentWords hk z
    (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
    (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk))
      (witnessBalancePackingPositionTensor hk z hd (PiTensorProduct.map (squareWords hk z) q))=_
  rw [witnessBalancePackingPositionTensor_projection hk z hd]
  have he : (witnessBalancePackingPositionTensor hk z hd).toLinearMap.comp
      ((PiTensorProduct.map (fun a : witnessBalancePackingLabelIndex k delta =>
        coordinateProjection (witnessBalanceLocalPairWords hk z a.val))).comp
          (PiTensorProduct.map (squareWords hk z)))=
      witnessBalancePackingProjectedSquareWords hk z hd := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    funext w
    simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,PiTensorProduct.map_tprod]
    change witnessBalancePackingPositionTensor hk z hd
      (PiTensorProduct.tprod ℂ (fun a =>
        coordinateProjection (witnessBalanceLocalPairWords hk z a.val) (squareWords hk z a (x a)))) w=
      witnessBalancePackingTensorWords hk z hd
        (PiTensorProduct.map (squareQuotient hk z) (PiTensorProduct.tprod ℂ x)) w
    rw [PiTensorProduct.map_tprod,witnessBalancePackingPositionTensor_tprod,
      witnessBalancePackingTensorWords_tprod]
    apply Finset.prod_congr rfl
    intro a _
    exact congrFun (squareQuotient_value hk z a (x a)).symm _
  exact DFunLike.congr_fun he q

/-- Both decoded physical letters on pure vectors of all local squares. -/
theorem witnessBalancePackingSquareWords_tprod_tmul_value (hd : delta ≤ 1)
    (x y : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceComponentRows hk z a.val).toSubmodule)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    witnessBalancePackingSquareWords hk z hd
      (PiTensorProduct.tprod ℂ (fun a => x a ⊗ₜ[ℂ] y a)) w=
      ∏ a, (x a).val (splitLeft (witnessBalancePackingPairRestriction hk z hd w a))*
        (y a).val (splitRight (witnessBalancePackingPairRestriction hk z hd w a)) := by
  rw [witnessBalancePackingSquareWords,LinearMap.comp_apply,PiTensorProduct.map_tprod]
  change witnessBalancePackingPositionTensor hk z hd
    (PiTensorProduct.tprod ℂ (fun a => squareWords hk z a (x a ⊗ₜ[ℂ] y a))) w=_
  rw [witnessBalancePackingPositionTensor_tprod]
  apply Finset.prod_congr rfl
  intro a _
  change wordTensor _ _ _ ((x a).val ⊗ₜ[ℂ] (y a).val)
    (witnessBalancePackingPairRestriction hk z hd w a)=_
  rw [wordTensor_tmul]

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingSquareWords
#print axioms HSTZ.witnessBalancePackingProjectedSquareWords
#print axioms HSTZ.witnessBalancePackingProjectedSquareWords_range
#print axioms HSTZ.witnessBalancePackingSquareWords_projection

#print axioms HSTZ.witnessBalancePackingSquareWords_tprod_tmul_value
