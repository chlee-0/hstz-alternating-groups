import HSTZ.ContainedProductSupport

/-! Finite-module instances for multiplicity spaces and sectors.
No dimension equality or classification is used. -/
namespace HSTZ

instance coreMultiplicityFinite {G H U V : Type*} [Group G] [Group H]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ U] [Module.Finite ℂ V]
    (rho : Representation ℂ G U) (tau : Representation ℂ (G × H) V) :
    Module.Finite ℂ (coreMultiplicity rho tau) := by
  let inclusion : coreMultiplicity rho tau →ₗ[ℂ] (U →ₗ[ℂ] V) :=
    { toFun := fun f => f.toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective inclusion
    (Representation.IntertwiningMap.toLinearMap_injective rho
      (tau.comp (MonoidHom.inl G H)))

/-- The native Specht block multiplicity carrier is finite over ℂ. -/
theorem blockMultiplicity_finite {n a b : ℕ} {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau a nu) (t : OAI.Saxl.Tableau n mu)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    Module.Finite ℂ
      (coreMultiplicity (OAI.Saxl.spechtRep s)
        ((OAI.Saxl.spechtRep t).comp (sumPermHom e))) := inferInstance

/-- Every complementary sector has a finite native carrier. This covers, but
does not assume, irreducibility of the sector selected by Maschke's theorem. -/
theorem blockComplementSector_finite {n a b : ℕ} {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau a nu) (t : OAI.Saxl.Tableau n mu)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (S : Subrepresentation (blockComplement s t e)) :
    Module.Finite ℂ S.toSubmodule := inferInstance

end HSTZ
#print axioms HSTZ.coreMultiplicityFinite
#print axioms HSTZ.blockMultiplicity_finite
#print axioms HSTZ.blockComplementSector_finite
