import OAI.RepresentationTheory.Saxl.SpechtClassification

import HSTZ.MultiplicityFinite

/-! Identify finite complementary sectors with canonical native Specht
carriers, through categorical isomorphisms and bijective intertwiners. -/
namespace HSTZ
open CategoryTheory
noncomputable section

/-- Classification gives an equivariant bijection, not only a shape or
character equality. This categorical interface requires carriers in `Type 0`. -/
theorem irreducible_specht_intertwiner {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (rho : Representation ℂ (Equiv.Perm (Fin n)) V)
    [Representation.IsIrreducible rho] :
    ∃ p : Nat.Partition n, ∃ j : Representation.IntertwiningMap rho
      (OAI.Saxl.spechtRep (OAI.Saxl.partitionTableau p)), Function.Bijective j := by
  obtain ⟨p, ⟨i⟩⟩ := OAI.Saxl.irreducible_equiv_specht rho
  exact ⟨p, i.toIntertwiningMap, i.toLinearEquiv.bijective⟩

/-- The selected finite multiplicity sector is identified with a complementary
Specht representation of the whole complement position group. -/
theorem blockComplementSector_specht {n a b : ℕ} {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau a nu) (t : OAI.Saxl.Tableau n mu)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (S : Subrepresentation (blockComplement s t e))
    [Representation.IsIrreducible S.toRepresentation] :
    ∃ p : Nat.Partition b, ∃ j : Representation.IntertwiningMap S.toRepresentation
      (OAI.Saxl.spechtRep (OAI.Saxl.partitionTableau p)), Function.Bijective j := by
  letI : Module.Finite ℂ S.toSubmodule := blockComplementSector_finite s t e S
  exact @irreducible_specht_intertwiner b S.toSubmodule
    inferInstance inferInstance inferInstance S.toRepresentation inferInstance

end
end HSTZ
#print axioms HSTZ.irreducible_specht_intertwiner
#print axioms HSTZ.blockComplementSector_specht
