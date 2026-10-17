import HSTZ.IntertwiningCompat
import HSTZ.TensorInterfaces
import HSTZ.WitnessBalanceComponents
import HSTZ.SpechtTensorWords

/-! Both component carriers in the full original diagonal square.
Adapts `BalanceColumns` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0) and reuses
its tensor inclusion and equivariance declarations. No packing identification is made here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessBalanceSpechtInclusion {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    Representation.IntertwiningMap (witnessBalanceLocalRows hk z).toRepresentation
      ((spechtRep z).comp (witnessBalanceGroup hk z).subtype) where
  toLinearMap :=
    { toFun := fun x => ⟨x.val,witnessBalance_local_mem_specht hk z x⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  isIntertwining' _ := LinearMap.ext fun _ => Subtype.ext rfl

theorem witnessBalanceSpechtInclusion_injective {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    Function.Injective (witnessBalanceSpechtInclusion hk z) := by
  intro x y he
  exact Subtype.ext (congrArg (fun a : Specht z => a.val) he)

def witnessBalanceSquareInclusion {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    Representation.IntertwiningMap
      ((witnessBalanceLocalRows hk z).toRepresentation.tprod
        (witnessBalanceLocalRows hk z).toRepresentation)
      (((spechtRep z).tprod (spechtRep z)).comp (witnessBalanceGroup hk z).subtype) where
  toLinearMap := TensorProduct.map (witnessBalanceSpechtInclusion hk z).toLinearMap
    (witnessBalanceSpechtInclusion hk z).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let F := witnessBalanceSpechtInclusion hk z
    have heq : (TensorProduct.map F.toLinearMap F.toLinearMap).comp
        (((witnessBalanceLocalRows hk z).toRepresentation.tprod
          (witnessBalanceLocalRows hk z).toRepresentation) g)=
      (((spechtRep z).tprod (spechtRep z)) g.val).comp
        (TensorProduct.map F.toLinearMap F.toLinearMap) := by
      ext x y
      change F ((witnessBalanceLocalRows hk z).toRepresentation g x) ⊗ₜ[ℂ]
        F ((witnessBalanceLocalRows hk z).toRepresentation g y)=
        spechtRep z g.val (F x) ⊗ₜ[ℂ] spechtRep z g.val (F y)
      rw [Representation.IntertwiningMap.isIntertwining _ _ F,
        Representation.IntertwiningMap.isIntertwining _ _ F]
      rfl
    exact DFunLike.congr_fun heq v

theorem witnessBalanceSquareInclusion_injective {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    Function.Injective (witnessBalanceSquareInclusion hk z) :=
  TensorProduct.map_injective_of_flat_flat _ _
    (witnessBalanceSpechtInclusion_injective hk z)
    (witnessBalanceSpechtInclusion_injective hk z)

private def witnessBalanceSquareWords {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    Representation.IntertwiningMap
      (((spechtRep z).tprod (spechtRep z)).comp (witnessBalanceGroup hk z).subtype)
      ((wordRep n ((witnessDiagram k b delta hk).colLen 0 *
        (witnessDiagram k b delta hk).colLen 0)).comp (witnessBalanceGroup hk z).subtype) where
  toLinearMap := ((wordTensorIntertwiner n _ _).comp (spechtTensorInclusion z z)).toLinearMap
  isIntertwining' g := LinearMap.ext fun v =>
    ((wordTensorIntertwiner n _ _).comp (spechtTensorInclusion z z)).map_action g.val v

def witnessBalanceTensorMap {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :=
  (witnessBalanceSquareWords hk z).comp (witnessBalanceSquareInclusion hk z)

theorem witnessBalanceTensorMap_tmul {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (x y : (witnessBalanceLocalRows hk z).toSubmodule) :
    witnessBalanceTensorMap hk z (x ⊗ₜ[ℂ] y)=wordTensor n _ _ (x.val ⊗ₜ[ℂ] y.val) := rfl

theorem witnessBalanceTensorMap_injective {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    Function.Injective (witnessBalanceTensorMap hk z) :=
  (wordTensor n _ _).injective.comp
    ((spechtTensorInclusion_injective z z).comp (witnessBalanceSquareInclusion_injective hk z))

/-- Preimage in the original full square; no cyclicity of the repeated vector is used. -/
theorem witnessBalanceTensorMap_full_square {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (v : (witnessBalanceLocalRows hk z).toSubmodule ⊗[ℂ]
      (witnessBalanceLocalRows hk z).toSubmodule) :
    ∃ q : Specht z ⊗[ℂ] Specht z,
      ((wordTensorIntertwiner n _ _).comp (spechtTensorInclusion z z)) q=
        witnessBalanceTensorMap hk z v :=
  ⟨witnessBalanceSquareInclusion hk z v,rfl⟩

def witnessBalanceOutputSum {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (label : ℕ) : ℤ :=
  2*witnessBalanceRowSum hk z label + (witnessBalancePositions hk z label).card

def witnessBalanceFixedOutputs {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    Submodule ℂ (WordSpace n ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0)) where
  carrier := {x | ∀ w, x w≠0 → ∀ label,
    (∑ i ∈ witnessBalancePositions hk z label, (balancePairOutput (w i) : ℤ))=
      witnessBalanceOutputSum hk z label}
  zero_mem' := by intro w h; exact False.elim (h rfl)
  add_mem' := by
    intro x y hx hy w hw label
    by_cases hh : x w=0
    · exact hy w (by intro hz; apply hw; simp [hh,hz]) label
    · exact hx w hh label
  smul_mem' := by
    intro a x hx w hw label
    exact hx w (by intro hz; apply hw; simp [hz]) label

theorem witnessBalanceTensorMap_output_sums {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (v : (witnessBalanceLocalRows hk z).toSubmodule ⊗[ℂ]
      (witnessBalanceLocalRows hk z).toSubmodule) :
    witnessBalanceTensorMap hk z v∈witnessBalanceFixedOutputs hk z := by
  classical
  induction v using TensorProduct.induction_on with
  | zero =>
    change (witnessBalanceTensorMap hk z).toLinearMap 0∈witnessBalanceFixedOutputs hk z
    rw [(witnessBalanceTensorMap hk z).toLinearMap.map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy =>
    change (witnessBalanceTensorMap hk z).toLinearMap (x+y)∈witnessBalanceFixedOutputs hk z
    rw [(witnessBalanceTensorMap hk z).toLinearMap.map_add x y]
    exact Submodule.add_mem _ hx hy
  | tmul x y =>
    intro w hw label
    rw [witnessBalanceTensorMap_tmul,wordTensor_tmul] at hw
    obtain ⟨hx,hy⟩ := mul_ne_zero_iff.mp hw
    have hleft := witnessBalance_local_sums hk z x
      (splitLeft (d := (witnessDiagram k b delta hk).colLen 0)
        (e := (witnessDiagram k b delta hk).colLen 0) w) hx label
    have hright := witnessBalance_local_sums hk z y
      (splitRight (d := (witnessDiagram k b delta hk).colLen 0)
        (e := (witnessDiagram k b delta hk).colLen 0) w) hy label
    simp only [balancePairOutput,Nat.cast_add,Nat.cast_one,Finset.sum_add_distrib,
      Finset.sum_const,nsmul_eq_mul,mul_one]
    change (∑ i ∈ witnessBalancePositions hk z label,
      ((splitLeft (d := (witnessDiagram k b delta hk).colLen 0)
        (e := (witnessDiagram k b delta hk).colLen 0) w i).val : ℤ)) +
      (∑ i ∈ witnessBalancePositions hk z label,
      ((splitRight (d := (witnessDiagram k b delta hk).colLen 0)
        (e := (witnessDiagram k b delta hk).colLen 0) w i).val : ℤ)) +
      (witnessBalancePositions hk z label).card=_
    rw [hleft,hright]
    unfold witnessBalanceOutputSum
    ring

end
end HSTZ
#print axioms HSTZ.witnessBalanceSpechtInclusion_injective
#print axioms HSTZ.witnessBalanceSquareInclusion_injective
#print axioms HSTZ.witnessBalanceTensorMap_tmul
#print axioms HSTZ.witnessBalanceTensorMap_injective
#print axioms HSTZ.witnessBalanceTensorMap_full_square
#print axioms HSTZ.witnessBalanceTensorMap_output_sums
