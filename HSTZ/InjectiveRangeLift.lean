import HSTZ.IntertwiningCompat
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Inverse of an injective intertwiner on a stable subspace of its image.
Adapted from `CyclicTensor.intertwiningRangeEquiv` and `intertwiningLiftSubrep` in
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). The representation
equivalence bundle used there is replaced by explicit linear maps and pointwise
equivariance. No semisimplicity hypothesis is used. -/
namespace HSTZ
section
variable {R G X Y : Type*} [CommRing R] [Monoid G]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  {rho : Representation R G X} {sigma : Representation R G Y}

noncomputable def injectiveRangeLinearLift
    (f : Representation.IntertwiningMap rho sigma) (hf : Function.Injective f)
    (S : Subrepresentation sigma) (hS : S.toSubmodule ≤ f.toLinearMap.range) :
    S.toSubmodule →ₗ[R] X :=
  (LinearEquiv.ofInjective f.toLinearMap hf).symm.toLinearMap.comp
    (Submodule.inclusion hS)

theorem injectiveRangeLinearLift_encode
    (f : Representation.IntertwiningMap rho sigma) (hf : Function.Injective f)
    (S : Subrepresentation sigma) (hS : S.toSubmodule ≤ f.toLinearMap.range)
    (x : S.toSubmodule) : f (injectiveRangeLinearLift f hf S hS x) = x.val := by
  have h := congrArg (fun y : f.toLinearMap.range => y.val)
    ((LinearEquiv.ofInjective f.toLinearMap hf).apply_symm_apply
      (Submodule.inclusion hS x))
  exact h

noncomputable def injectiveRangeLift
    (f : Representation.IntertwiningMap rho sigma) (hf : Function.Injective f)
    (S : Subrepresentation sigma) (hS : S.toSubmodule ≤ f.toLinearMap.range) :
    Representation.IntertwiningMap S.toRepresentation rho where
  toLinearMap := injectiveRangeLinearLift f hf S hS
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply hf
    change f (injectiveRangeLinearLift f hf S hS (S.toRepresentation g x)) =
      f (rho g (injectiveRangeLinearLift f hf S hS x))
    calc
      f (injectiveRangeLinearLift f hf S hS (S.toRepresentation g x)) =
          sigma g x.val := injectiveRangeLinearLift_encode f hf S hS _
      _ = sigma g (f (injectiveRangeLinearLift f hf S hS x)) :=
        congrArg (fun z => sigma g z) (injectiveRangeLinearLift_encode f hf S hS x).symm
      _ = f (rho g (injectiveRangeLinearLift f hf S hS x)) :=
        (f.map_action g _).symm

theorem injectiveRangeLift_encode
    (f : Representation.IntertwiningMap rho sigma) (hf : Function.Injective f)
    (S : Subrepresentation sigma) (hS : S.toSubmodule ≤ f.toLinearMap.range)
    (x : S.toSubmodule) : f (injectiveRangeLift f hf S hS x) = x.val :=
  injectiveRangeLinearLift_encode f hf S hS x

theorem injectiveRangeLift_injective
    (f : Representation.IntertwiningMap rho sigma) (hf : Function.Injective f)
    (S : Subrepresentation sigma) (hS : S.toSubmodule ≤ f.toLinearMap.range) :
    Function.Injective (injectiveRangeLift f hf S hS) := by
  intro x y h
  apply Subtype.ext
  have he := congrArg (fun z : X => f z) h
  change f (injectiveRangeLift f hf S hS x) =
    f (injectiveRangeLift f hf S hS y) at he
  rwa [injectiveRangeLift_encode, injectiveRangeLift_encode] at he
end
end HSTZ
#print axioms HSTZ.injectiveRangeLift_encode
#print axioms HSTZ.injectiveRangeLift_injective
