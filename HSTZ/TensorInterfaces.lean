import OAI.RepresentationTheory.Saxl.StaircaseTensor
import HSTZ.IntertwiningCompat

/-! HSTZ interfaces extending the unmodified OpenAI tensor-square sources. -/

namespace OAI.Saxl
noncomputable section

def spechtTensorInclusion {n : ℕ} {μ ν : YoungDiagram}
    (s : Tableau n μ) (t : Tableau n ν) :
    Representation.IntertwiningMap ((spechtRep s).tprod (spechtRep t))
      ((wordRep n (μ.colLen 0)).tprod (wordRep n (ν.colLen 0))) :=
  (spechtInclusion s).tensor (spechtInclusion t)

lemma spechtTensorInclusion_injective {n : ℕ} {μ ν : YoungDiagram}
    (s : Tableau n μ) (t : Tableau n ν) : Function.Injective (spechtTensorInclusion s t) :=
  TensorProduct.map_injective_of_flat_flat _ _
    (spechtSub s).toSubmodule.subtype_injective (spechtSub t).toSubmodule.subtype_injective

def spechtSelfDualLinear {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Specht t ≃ₗ[ℂ] Module.Dual ℂ (Specht t) :=
  (spechtSelfDual t).toLinearEquiv

lemma spechtSelfDualLinear_equivariant {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n)) (v : Specht t) :
    spechtSelfDualLinear t (spechtRep t g v) =
      (spechtRep t).dual g (spechtSelfDualLinear t v) :=
  (spechtSelfDual t).toIntertwiningMap.map_action g v

end
end OAI.Saxl

#print axioms OAI.Saxl.spechtSelfDualLinear_equivariant
