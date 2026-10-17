import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalanceComponentProjection
import HSTZ.WitnessBalanceNeighborSupport

/-! Projected ranges of one original component and of the other factor.
Reuses APIs from OpenAI's `math` repository (commit adc7f1241) and Mathlib's tensor
range lemmas. No packing support is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (a : ℕ)

private def otherSquareWords : Representation.IntertwiningMap
    ((witnessBalanceOtherRows hk z a).toRepresentation.tprod
      (witnessBalanceOtherRows hk z a).toRepresentation)
    ((wordRep (witnessBalanceOtherSize hk z a) (witnessBalancePairDim k b delta hk)).comp
      (witnessBalanceOtherGroup hk z a).subtype) where
  toLinearMap := (wordTensor _ _ _).toLinearMap.comp
    (cyclicTensorInclusion ((wordRep _ _).comp (witnessBalanceOtherGroup hk z a).subtype)
      ((wordRep _ _).comp (witnessBalanceOtherGroup hk z a).subtype)
      (witnessBalanceOtherWord hk z a) (witnessBalanceOtherWord hk z a)).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    have he := (cyclicTensorInclusion ((wordRep _ _).comp (witnessBalanceOtherGroup hk z a).subtype)
      ((wordRep _ _).comp (witnessBalanceOtherGroup hk z a).subtype)
      (witnessBalanceOtherWord hk z a) (witnessBalanceOtherWord hk z a)).map_action (g,g) q
    exact (congrArg (wordTensor _ _ _) he).trans
      ((wordTensorIntertwiner _ _ _).map_action g.val _)

/-- The group of the remaining labels gives the covariance. -/
theorem witnessBalance_other_pair_invariant (g : witnessBalanceOtherGroup hk z a) w :
    witnessBalanceOtherPairWords hk z a (w ∘ g.val) ↔ witnessBalanceOtherPairWords hk z a w := by
  constructor
  · rintro ⟨hA,hL⟩
    exact ⟨fun i => by simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hA (g.val.symm i),
      fun i => by simpa only [Function.comp_apply,Equiv.apply_symm_apply] using
        (hL (g.val.symm i)).trans (g.property (g.val.symm i)).symm⟩
  · rintro ⟨hA,hL⟩
    exact ⟨fun i => hA (g.val i),fun i => (hL (g.val i)).trans (g.property i)⟩

private def otherProjection : Representation.IntertwiningMap
    ((wordRep (witnessBalanceOtherSize hk z a) (witnessBalancePairDim k b delta hk)).comp
      (witnessBalanceOtherGroup hk z a).subtype)
    ((wordRep (witnessBalanceOtherSize hk z a) (witnessBalancePairDim k b delta hk)).comp
      (witnessBalanceOtherGroup hk z a).subtype) where
  toLinearMap := coordinateProjection (witnessBalanceOtherPairWords hk z a)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext w
    change (if witnessBalanceOtherPairWords hk z a w then x (w ∘ g.val) else 0)=
      (if witnessBalanceOtherPairWords hk z a (w ∘ g.val) then x (w ∘ g.val) else 0)
    rw [witnessBalance_other_pair_invariant]

def witnessBalanceOtherProjectedMap := (otherProjection hk z a).comp (otherSquareWords hk z a)

def witnessBalanceLocalProjectedFactor : Subrepresentation
    (wordRep (witnessBalanceComponentSize hk z a) (witnessBalancePairDim k b delta hk)) where
  toSubmodule := (witnessBalanceLocalProjectedMap hk z a).toLinearMap.range
  apply_mem_toSubmodule g x hx := by
    obtain ⟨q,rfl⟩ := hx
    exact ⟨((witnessBalanceComponentRows hk z a).toRepresentation.tprod
      (witnessBalanceComponentRows hk z a).toRepresentation) g q,
      (witnessBalanceLocalProjectedMap hk z a).map_action g q⟩

def witnessBalanceOtherProjectedFactor : Subrepresentation
    ((wordRep (witnessBalanceOtherSize hk z a) (witnessBalancePairDim k b delta hk)).comp
      (witnessBalanceOtherGroup hk z a).subtype) where
  toSubmodule := (witnessBalanceOtherProjectedMap hk z a).toLinearMap.range
  apply_mem_toSubmodule g x hx := by
    obtain ⟨q,rfl⟩ := hx
    exact ⟨((witnessBalanceOtherRows hk z a).toRepresentation.tprod
      (witnessBalanceOtherRows hk z a).toRepresentation) g q,
      (witnessBalanceOtherProjectedMap hk z a).map_action g q⟩

private def pairedPositionMap : Representation.IntertwiningMap
    (independentTensor (wordRep (witnessBalanceComponentSize hk z a) (witnessBalancePairDim k b delta hk))
      ((wordRep (witnessBalanceOtherSize hk z a) (witnessBalancePairDim k b delta hk)).comp
        (witnessBalanceOtherGroup hk z a).subtype))
    (((wordRep n (witnessBalancePairDim k b delta hk)).comp (witnessBalanceGroup hk z).subtype).comp
      (witnessBalanceComponentHom hk z a)) where
  toLinearMap := (positionTensor (witnessBalanceComponentCut hk z a)).toLinearMap
  isIntertwining' gh := LinearMap.ext fun q =>
    positionTensor_equivariant (witnessBalanceComponentCut hk z a) gh.1 gh.2.val q

private def rangeInclusion : Representation.IntertwiningMap
    ((witnessBalanceProjectedRange hk z (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toRepresentation.comp (witnessBalanceComponentHom hk z a))
    (((wordRep n (witnessBalancePairDim k b delta hk)).comp (witnessBalanceGroup hk z).subtype).comp
      (witnessBalanceComponentHom hk z a)) where
  toLinearMap := Submodule.subtype _
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

def witnessBalanceProjectedFactorWords := (pairedPositionMap hk z a).comp
  (independentTensorMap (witnessBalanceLocalProjectedMap hk z a) (witnessBalanceOtherProjectedMap hk z a))

/-- The complete-neighbor target is the local factor. -/
theorem witnessBalance_neighbor_projected_factor (s : ℕ) :
    witnessBalanceLocalProjectedFactor hk z (3+s)=witnessBalanceNeighborProjectedSquare hk z s := by
  apply SetLike.ext
  intro x
  rfl

private def localFactorInclusion : Representation.IntertwiningMap
    (witnessBalanceLocalProjectedFactor hk z a).toRepresentation
    (wordRep (witnessBalanceComponentSize hk z a) (witnessBalancePairDim k b delta hk)) where
  toLinearMap := Submodule.subtype _
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

private def otherFactorInclusion : Representation.IntertwiningMap
    (witnessBalanceOtherProjectedFactor hk z a).toRepresentation
    ((wordRep (witnessBalanceOtherSize hk z a) (witnessBalancePairDim k b delta hk)).comp
      (witnessBalanceOtherGroup hk z a).subtype) where
  toLinearMap := Submodule.subtype _
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_other_pair_invariant
#print axioms HSTZ.witnessBalanceLocalProjectedFactor
#print axioms HSTZ.witnessBalanceOtherProjectedFactor
#print axioms HSTZ.witnessBalance_neighbor_projected_factor

