import HSTZ.SpechtPositionTransport
import HSTZ.WitnessBalancePackingAssemblyH
import HSTZ.WitnessBalanceProjectedFactors
import HSTZ.WitnessBalanceAverage
import HSTZ.WitnessBalanceFrontier

/-! Positivity from an injection of the target Specht module into the induction of
the assembly from the physical block group. Uses the same local instances as
`WitnessBalancePackingAssemblyH`, so that `AssemblyHReturn` composes without instance
unfolding. Uses declarations from OpenAI's `math` repository (commit adc7f1241,
Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))
local instance wbsrRestACG : AddCommGroup (witnessBalancePackingRestTensorSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance wbsrPairRestACG : AddCommGroup (witnessBalancePackingJointPairRestSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance wbsrPairRestModule : Module ℂ (witnessBalancePackingJointPairRestSpace hk z) := TensorProduct.leftModule
local instance wbsrAssemblyACG : AddCommGroup (witnessBalancePackingAssemblySpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- By Frobenius reciprocity and the projected range, an injection into the
induction from H gives positivity. -/
theorem witnessBalance_pos_of_H_injection (hd : delta ≤ 1) {mu : YoungDiagram}
    (s : Tableau n mu)
    (J0 : Representation.IntertwiningMap (spechtRep s)
      (Representation.ind (witnessBalanceGroup hk z).subtype
        (witnessBalancePackingJointPairRestHAction hk z hd)))
    (hJ0 : Function.Injective J0) : 0 < kronecker z z s := by
  haveI := specht_nontrivial s
  haveI : Finite (witnessBalanceGroup hk z) := Subtype.finite
  obtain ⟨bmap,hb⟩ := induced_restricted_nonzero (witnessBalanceGroup hk z).subtype
    (witnessBalancePackingJointPairRestHAction hk z hd) (spechtRep s) J0 hJ0
  have hP := witnessBalancePackingJointPairProjectedMap_bijective hk z hd
  have hf : (witnessBalancePackingJointPairProjectedMap hk z hd).comp bmap ≠ 0 := by
    intro hz
    apply hb
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply hP.1
    have hx := congrArg (fun F : Representation.IntertwiningMap _ _ => F x) hz
    change witnessBalancePackingJointPairProjectedMap hk z hd (bmap x) = 0 at hx
    exact hx.trans (witnessBalancePackingJointPairProjectedMap hk z hd).toLinearMap.map_zero.symm
  exact witnessBalance_kronecker_pos_of_projected hk z s hd
    ((witnessBalancePackingJointPairProjectedMap hk z hd).comp bmap) hf

/-- An injection into induction of the assembly along the physical block hom gives positivity. -/
theorem witnessBalance_pos_of_assembly_injection (hd : delta ≤ 1) {mu : YoungDiagram}
    (s : Tableau n mu)
    (E : Representation.IntertwiningMap (spechtRep s)
      (Representation.ind (witnessBalancePackingCoarserHom hk z hd)
        (witnessBalancePackingAssemblyAction hk z)))
    (hE : Function.Injective E) : 0 < kronecker z z s :=
  witnessBalance_pos_of_H_injection hk z hd s
    ((witnessBalancePackingAssemblyHReturn hk z hd).comp E)
    ((witnessBalancePackingAssemblyHReturn_bijective hk z hd).1.comp hE)
end

end
end HSTZ
#print axioms HSTZ.witnessBalance_pos_of_H_injection
#print axioms HSTZ.witnessBalance_pos_of_assembly_injection
