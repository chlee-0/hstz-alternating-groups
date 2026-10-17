import HSTZ.ComplementSpecht
import HSTZ.InducedComplementTransport

/-! Arbitrary contained targets occur in ordinary induction of Specht factors.
The complement is classified through its finite irreducible multiplicity carrier, so no
complementary shape or trivial action is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem induced_embedding_classify_complement
    {G A U W V : Type} {b : ℕ} [Group G] [Finite G] [Group A]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] [AddCommGroup V] [Module ℂ V]
    (phi : G × Equiv.Perm (Fin b) →* A) (rho : Representation ℂ G U)
    (sigma : Representation ℂ (Equiv.Perm (Fin b)) W) (tau : Representation ℂ A V)
    [Representation.IsIrreducible sigma]
    (E : Representation.IntertwiningMap tau
      (Representation.ind phi (independentTensor rho sigma))) (hE : Function.Injective E) :
    ∃ p : Nat.Partition b, ∃ F : Representation.IntertwiningMap tau
      (Representation.ind phi (independentTensor rho (spechtRep (partitionTableau p)))),
      Function.Injective F := by
  obtain ⟨p, j, hj⟩ := irreducible_specht_intertwiner sigma
  obtain ⟨F, hF⟩ := product_induced_embedding_transport_complement
    phi rho sigma (spechtRep (partitionTableau p)) tau j hj.1 E hE
  exact ⟨p, F, hF⟩

/-- Fully typed specialization: it keeps the original target Specht module and chooses
a complementary partition internally. -/
def contained_specht_embedding_of_containment {n a b : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu)
    (e : Fin n ≃ Fin a ⊕ Fin b) := by
  let chosen := contained_product_embedding_of_containment s t h e
  let S := Classical.choose chosen
  have hS : Representation.IsIrreducible S.toRepresentation :=
    (Classical.choose_spec chosen).1
  let chosenE := (Classical.choose_spec chosen).2
  let E := Classical.choose chosenE
  have hE : Function.Injective E := Classical.choose_spec chosenE
  letI := hS
  letI : Module.Finite ℂ S.toSubmodule :=
    blockComplementSector_finite s (containedBlockTableau s t h e) e S
  exact @induced_embedding_classify_complement
    (Equiv.Perm (Fin a)) (Equiv.Perm (Fin n))
    (Specht s) S.toSubmodule (Specht t) b
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (sumPermHom e) (spechtRep s) S.toRepresentation (spechtRep t)
    hS E hE

end
end HSTZ
#print axioms HSTZ.induced_embedding_classify_complement
#check HSTZ.contained_specht_embedding_of_containment
#print axioms HSTZ.contained_specht_embedding_of_containment
