import HSTZ.ContainedMultiplicity
import HSTZ.MultiplicityInduction
import HSTZ.TableauAlignment

/-! Support of the contained target in full-product ordinary induction.
The selected complement is an irreducible multiplicity sector; its
identification with a Specht representation is a separate step, not made here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

abbrev blockComplement {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (e : Fin n ≃ Fin a ⊕ Fin b) :=
  complementMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e))

abbrev blockMultiplicityTensor {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (e : Fin n ≃ Fin a ⊕ Fin b)
    (S : Subrepresentation (blockComplement s t e)) :
    Representation ℂ (Equiv.Perm (Fin a) × Equiv.Perm (Fin b))
      (Specht s ⊗[ℂ] S.toSubmodule) :=
  independentTensor (spechtRep s) S.toRepresentation

abbrev blockMultiplicityInduced {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (e : Fin n ≃ Fin a ⊕ Fin b)
    (S : Subrepresentation (blockComplement s t e)) := by
  letI : AddCommGroup (Specht s ⊗[ℂ] S.toSubmodule) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht s ⊗[ℂ] S.toSubmodule) := TensorProduct.leftModule
  exact Representation.ind (A := Specht s ⊗[ℂ] S.toSubmodule) (sumPermHom e)
    (blockMultiplicityTensor s t e S)

/-- This proof-valued definition specializes the generic theorem
`product_induced_embedding_of_core`. Its type is inferred: it selects an
irreducible sector and a target injection into ordinary block induction. -/
def contained_product_embedding {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (hi : tableauInclusion s t h = blockInclusion e) :=
  @product_induced_embedding_of_core
    (Equiv.Perm (Fin a)) (Equiv.Perm (Fin b)) (Equiv.Perm (Fin n))
    (Specht s) (Specht t)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (sumPermHom e) (spechtRep s) (spechtRep t) (specht_irreducible t)
    (Classical.choose (exists_nonzero_blockCoreMap s t h e hi))
    (Classical.choose_spec (exists_nonzero_blockCoreMap s t h e hi))

/-- Placement chosen internally for the contained tableau. -/
def containedBlockTableau {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu)
    (e : Fin n ≃ Fin a ⊕ Fin b) : Tableau n mu :=
  Classical.choose (exists_block_tableau s t h e)

theorem containedBlockTableau_matching {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    tableauInclusion s (containedBlockTableau s t h e) h = blockInclusion e :=
  Classical.choose_spec (exists_block_tableau s t h e)

/-- Proof-valued definition whose inferred type keeps the original target
Specht module, using a placement-preserving tableau transport; no matching
hypothesis is required. -/
def contained_product_embedding_of_containment {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu)
    (e : Fin n ≃ Fin a ⊕ Fin b) :=
  @product_induced_embedding_precompose
    (Equiv.Perm (Fin a)) (Equiv.Perm (Fin b)) (Equiv.Perm (Fin n))
    (Specht s) (Specht (containedBlockTableau s t h e)) (Specht t)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (sumPermHom e) (spechtRep s) (spechtRep (containedBlockTableau s t h e))
    (specht_irreducible (containedBlockTableau s t h e))
    (Classical.choose (exists_nonzero_blockCoreMap s (containedBlockTableau s t h e) h e
      (containedBlockTableau_matching s t h e)))
    (Classical.choose_spec (exists_nonzero_blockCoreMap s (containedBlockTableau s t h e) h e
      (containedBlockTableau_matching s t h e)))
    (spechtRep t) (tableauSpechtMap t (containedBlockTableau s t h e))
    (tableauSpechtMap_bijective t (containedBlockTableau s t h e)).1

end
end HSTZ
#check HSTZ.contained_product_embedding
#print axioms HSTZ.contained_product_embedding

#check HSTZ.contained_product_embedding_of_containment
#print axioms HSTZ.containedBlockTableau_matching
#print axioms HSTZ.contained_product_embedding_of_containment
