import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalancePackingFactorization

/-! Return from the original source to the joint induced pair tensor with the
entire rest. Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This is a concrete composition of the existing source reparametrization and
factorization; `K` is larger than `H`. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))
local instance : AddCommGroup (witnessBalancePackingRestTensorSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup (witnessBalancePackingJointPairRestSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : Module ℂ (witnessBalancePackingJointPairRestSpace hk z) := TensorProduct.leftModule

private def sourceLinear :
    Representation.IndV (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
      (witnessBalancePackingJointPairRestAction hk z) →ₗ[ℂ]
    witnessBalancePackingAssemblySpace hk z :=
  (witnessBalancePackingFactorization hk z).toLinearMap.comp
    (witnessBalancePackingProductInduction hk z).toLinearMap

/-- Source return, keeping the independent original labels and all of the rest. -/
def witnessBalancePackingAssemblyReturn : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
      (witnessBalancePackingJointPairRestAction hk z)) (witnessBalancePackingAssemblyAction hk z) where
  toLinearMap := sourceLinear hk z
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    change witnessBalancePackingFactorization hk z
      (witnessBalancePackingProductInduction hk z
        (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
          (witnessBalancePackingJointPairRestAction hk z) g q)) =
      witnessBalancePackingAssemblyAction hk z g
        (witnessBalancePackingFactorization hk z (witnessBalancePackingProductInduction hk z q))
    calc
      witnessBalancePackingFactorization hk z
        (witnessBalancePackingProductInduction hk z
          (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
            (witnessBalancePackingJointPairRestAction hk z) g q)) =
        witnessBalancePackingFactorization hk z
          (Representation.ind (k:=ℂ) (witnessBalancePackingProductToCoarser hk z)
            (witnessBalancePackingProductAction hk z) g
              (witnessBalancePackingProductInduction hk z q)) :=
        congrArg (fun x => witnessBalancePackingFactorization hk z x)
          ((witnessBalancePackingProductInduction hk z).map_action g q)
      _ = _ := (witnessBalancePackingFactorization hk z).map_action g
        (witnessBalancePackingProductInduction hk z q)

theorem witnessBalancePackingAssemblyReturn_bijective :
    Function.Bijective (witnessBalancePackingAssemblyReturn hk z) := by
  change Function.Bijective ((witnessBalancePackingFactorization hk z) ∘
    (witnessBalancePackingProductInduction hk z))
  exact (witnessBalancePackingFactorization_bijective hk z).comp
    (witnessBalancePackingProductInduction_bijective hk z)

theorem witnessBalancePackingAssemblyReturn_mk
    (g : Equiv.Perm (Fin (witnessBalancePackingJointDegree hk z)))
    (r : witnessBalancePackingRestGroup hk z) (v : witnessBalancePackingJointPairSpace hk z)
    (w : witnessBalancePackingRestTensorSpace hk z) :
    witnessBalancePackingAssemblyReturn hk z
      (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
        (witnessBalancePackingJointPairRestAction hk z) (g,r) (v ⊗ₜ[ℂ] w))=
    Representation.IndV.mk (k:=ℂ) (sumPermHom finSumFinEquiv.symm)
      (independentTensor (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation
        (witnessBalanceLocalProjectedFactor hk z (witnessBalancePackingJointLabel delta)).toRepresentation)
      g v ⊗ₜ[ℂ] witnessBalancePackingRestProductAction hk z r⁻¹ w := by
  change witnessBalancePackingFactorization hk z
    (witnessBalancePackingProductInduction hk z _) = _
  rw [witnessBalancePackingProductInduction_mk, witnessBalancePackingFactorization_mk]
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingAssemblyReturn
#print axioms HSTZ.witnessBalancePackingAssemblyReturn_bijective
#print axioms HSTZ.witnessBalancePackingAssemblyReturn_mk
