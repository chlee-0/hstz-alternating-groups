import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Intertwining

/-! Identity transport between equal stable subspaces. -/
namespace HSTZ
section EqualSubrepresentations
variable {R G V : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
  {rho : Representation R G V}

/-- Transport along equality preserves the ambient vector and group action. -/
noncomputable def equalSubrepresentationMap (P Q : Subrepresentation rho) (he : P = Q) :
    Representation.IntertwiningMap P.toRepresentation Q.toRepresentation where
  toLinearMap :=
    { toFun := fun x => ⟨x.val, by
        change x.val ∈ Q.toSubmodule
        rw [← he]
        exact x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

theorem equalSubrepresentationMap_val (P Q : Subrepresentation rho) (he : P = Q)
    (x : P.toSubmodule) :
    ((equalSubrepresentationMap P Q he) x).val = x.val := rfl

theorem equalSubrepresentationMap_bijective (P Q : Subrepresentation rho) (he : P = Q) :
    Function.Bijective (equalSubrepresentationMap P Q he).toLinearMap := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Q.toSubmodule => z.val) hxy
  · intro y
    have hy : y.val ∈ P.toSubmodule := by
      rw [he]
      exact y.property
    exact ⟨⟨y.val, hy⟩, rfl⟩
end EqualSubrepresentations

end HSTZ
#print axioms HSTZ.equalSubrepresentationMap_val
#print axioms HSTZ.equalSubrepresentationMap_bijective
