import HSTZ.IntertwiningCompat
import HSTZ.ContainedRestriction
import HSTZ.BlockCoreAction
import HSTZ.MultiplicityConstituent

/-! Nonzero block-core multiplicity from contained Specht branching.
The complement is fixed pointwise only in the core restriction; its full
commuting action remains on the multiplicity space. -/
namespace HSTZ
open OAI.Saxl

/-- Rebundle a contained-core map under the equal first-block action. -/
noncomputable def blockCoreMap {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (hi : tableauInclusion s t h = blockInclusion e)
    (j : Representation.IntertwiningMap (spechtRep s)
      ((spechtRep t).comp (Equiv.Perm.viaEmbeddingHom (tableauInclusion s t h)))) :
    coreMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e)) where
  toLinearMap := j.toLinearMap
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro x
    change j (spechtRep s g x) = spechtRep t (sumPermHom e (g,1)) (j x)
    rw [sumPermHom_core, ← hi]
    exact j.map_action g x

/-- Arbitrary containment gives nonzero core multiplicity for the full
product-block restriction, when the tableau is placed on that block. -/
theorem exists_nonzero_blockCoreMap {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (hi : tableauInclusion s t h = blockInclusion e) :
    ∃ f : coreMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e)), f ≠ 0 := by
  obtain ⟨j, hj⟩ := contained_restricted_embedding s t h
  let f := blockCoreMap s t h e hi j
  refine ⟨f, ?_⟩
  let p : Specht s := ⟨polytabloid s, mem_cyclic _ _⟩
  intro hz
  have hp : j p = 0 := congrArg
    (fun L : coreMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e)) => L p) hz
  have hp0 : p = 0 := hj (hp.trans (map_zero j.toLinearMap).symm)
  exact polytabloid_ne_zero s (congrArg Subtype.val hp0)

end HSTZ
#print axioms HSTZ.blockCoreMap
#print axioms HSTZ.exists_nonzero_blockCoreMap
