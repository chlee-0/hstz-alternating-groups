import HSTZ.WitnessBalancePackingInterchange

/-! Both finite C-factor layers map back to the original native `J` and `P J` images.
Reuses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This is the square of `RowsWords`; compatibility with the independent local-square
interchange is a separate obligation, not proved here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
  (z : Tableau n (witnessDiagram k b delta hk))

def witnessBalancePackingRowsSquareWords (hd : delta ≤ 1) :
    (witnessBalancePackingRowsSpace hk z ⊗[ℂ] witnessBalancePackingRowsSpace hk z) →ₗ[ℂ]
      WordSpace n (witnessBalancePairDim k b delta hk) :=
  (wordTensor n ((witnessDiagram k b delta hk).colLen 0)
    ((witnessDiagram k b delta hk).colLen 0)).toLinearMap.comp
      (TensorProduct.map (witnessBalancePackingRowsWords hk z hd) (witnessBalancePackingRowsWords hk z hd))

private theorem originalTensorMap_equation :
    (witnessBalanceTensorMap hk z).toLinearMap=
      (wordTensor n ((witnessDiagram k b delta hk).colLen 0)
        ((witnessDiagram k b delta hk).colLen 0)).toLinearMap.comp
          (TensorProduct.mapIncl (witnessBalanceLocalRows hk z).toSubmodule
            (witnessBalanceLocalRows hk z).toSubmodule) := by
  apply TensorProduct.ext'
  intro x y
  rfl

/-- The original native `J` image from both finite component-carrier layers. -/
theorem witnessBalancePackingRowsSquareWords_range (hd : delta ≤ 1) :
    (witnessBalancePackingRowsSquareWords hk z hd).range=
      (witnessBalanceTensorMap hk z).toLinearMap.range := by
  rw [witnessBalancePackingRowsSquareWords,originalTensorMap_equation,
    LinearMap.range_comp,LinearMap.range_comp,TensorProduct.range_map,
    witnessBalancePackingRowsWords_range,
    TensorProduct.range_mapIncl]

def witnessBalancePackingRowsProjectedSquareWords (hd : delta ≤ 1) :
    (witnessBalancePackingRowsSpace hk z ⊗[ℂ] witnessBalancePackingRowsSpace hk z) →ₗ[ℂ]
      WordSpace n (witnessBalancePairDim k b delta hk) :=
  (witnessBalanceComponentProjection hk z
    (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
    (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toLinearMap.comp
      (witnessBalancePackingRowsSquareWords hk z hd)

/-- The original `P J` image for this normalized `RowsWords`-square source. Equality
with the tensor of local projected factors still needs the interchange word map. -/
theorem witnessBalancePackingRowsProjectedSquareWords_range (hd : delta ≤ 1) :
    (witnessBalancePackingRowsProjectedSquareWords hk z hd).range=
      (witnessBalanceProjectedRange hk z
        (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
        (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toSubmodule := by
  change ((witnessBalanceComponentProjection hk z
    (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
    (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toLinearMap.comp
      (witnessBalancePackingRowsSquareWords hk z hd)).range=
    ((witnessBalanceComponentProjection hk z
      (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toLinearMap.comp
        (witnessBalanceTensorMap hk z).toLinearMap).range
  rw [LinearMap.range_comp,LinearMap.range_comp,witnessBalancePackingRowsSquareWords_range hk z hd]

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingRowsSquareWords
#print axioms HSTZ.witnessBalancePackingRowsSquareWords_range
#print axioms HSTZ.witnessBalancePackingRowsProjectedSquareWords
#print axioms HSTZ.witnessBalancePackingRowsProjectedSquareWords_range
