import HSTZ.TensorSquareCovering
import HSTZ.TauCetiFinite.EvenMultiplicity
import HSTZ.TauCetiFinite.RestrictionNorm
import HSTZ.TauCetiFinite.DegreeFiveMoments
import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Adjunction
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Maschke

/-!
The finite-range representation argument, joined to the large-degree proof only through
`HSTZ.TensorSquareCovering`. All multiplicities are dimensions of intertwiner spaces.
The whole S_n Specht module embeds in X ⊕ (sgn ⊗ X) before restriction; consequently
every simple A_n constituent embeds in X ⊕ X, and one of its two projections is nonzero.
Coverage of both split constituents is not inferred from a map out of a reducible
restricted Specht module.

Uses TauCeti's Specht classification, Maschke splitting and induction/reciprocity results.
-/
namespace HSTZ.TauCetiFinite
noncomputable section
open CategoryTheory
open scoped Classical TensorProduct

/-- Every simple A_n object embeds in the restriction of some whole S_n Specht.
Induce it, choose an irreducible subrepresentation, split that inclusion by
Maschke, and apply Frobenius reciprocity to the resulting nonzero quotient. -/
theorem exists_nonzero_hom_restrictedSpecht {n : ℕ}
    (A : FDRep ℂ (alternatingGroup (Fin n))) [Simple A] :
    ∃ nu : Nat.Partition n, ∃ f : A ⟶ restrictedSpecht nu, f ≠ 0 := by
  let H := alternatingGroup (Fin n)
  let I := TauCeti.indFDRep A
  haveI : Representation.IsIrreducible A.ρ := FDRep.isIrreducible_of_simple A
  haveI : Nontrivial A :=
    Representation.IsIrreducible.nontrivial (ρ := A.ρ) inferInstance
  have hI : 0 < Module.finrank ℂ I := by
    rw [show Module.finrank ℂ I = H.index * Module.finrank ℂ A from
      TauCeti.finrank_indFDRep A]
    exact Nat.mul_pos (Nat.pos_of_ne_zero H.index_ne_zero_of_finite)
      Module.finrank_pos
  haveI : Nontrivial I := Module.nontrivial_of_finrank_pos hI
  obtain ⟨tau, htau⟩ := Representation.exists_isAtom I.ρ
  haveI : Representation.IsIrreducible tau.toRepresentation :=
    Representation.isIrreducible_toRepresentation_of_isAtom htau
  haveI : Nontrivial tau.toSubmodule :=
    Representation.IsIrreducible.nontrivial (ρ := tau.toRepresentation) inferInstance
  let B := FDRep.of tau.toRepresentation
  haveI : Representation.IsIrreducible B.ρ := by
    change Representation.IsIrreducible tau.toRepresentation
    infer_instance
  haveI : Simple B := FDRep.simple_of_isIrreducible B
  obtain ⟨nu, ⟨e⟩, _⟩ := TauCeti.existsUnique_nonempty_iso_spechtModuleℂ B
  obtain ⟨p, hp⟩ := tau.subtype.exists_leftInverse_of_injective tau.subtype_injective
  have hp0 : p ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : tau.toSubmodule)
    have hh := congrArg (fun f => f x) hp
    have hx0 : x = 0 := by simpa [hz] using hh.symm
    exact hx hx0
  let q : I ⟶ B := FDRep.forget₂HomLinearEquiv I B (Rep.ofHom p)
  have hq : q ≠ 0 := by
    intro hz
    apply hp0
    apply Representation.IntertwiningMap.ext
    have hh := congrArg (fun f : I ⟶ B => f.hom.hom.hom) hz
    exact hh
  let r : A ⟶ Subgroup.resFDRep H B := FDRep.indResFDRepHomEquiv A B q
  have hr : r ≠ 0 := by
    intro hz
    apply hq
    exact (FDRep.indResFDRepHomEquiv A B).injective
      (hz.trans (map_zero (FDRep.indResFDRepHomEquiv A B)).symm)
  let R := Action.res (FGModuleCat ℂ) H.subtype
  refine ⟨nu, r ≫ R.map e.hom, ?_⟩
  intro hz
  change (r ≫ R.map e.hom : A ⟶ R.obj (TauCeti.spechtModuleℂ nu)) =
    (0 : A ⟶ R.obj (TauCeti.spechtModuleℂ nu)) at hz
  apply hr
  apply (cancel_mono (R.map e.hom)).mp
  rw [CategoryTheory.Limits.zero_comp]
  exact hz

/-- Restriction makes the scalar sign twist identical to the original action. -/
theorem signTwist_comp_alternating {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    (signTwist ρ).comp (alternatingGroup (Fin n)).subtype =
      ρ.comp (alternatingGroup (Fin n)).subtype := by
  ext g v
  have hs := Equiv.Perm.mem_alternatingGroup.mp g.property
  simp [signTwist, hs]

/-- The restricted cover is literally a product of two copies of the square. -/
theorem evenSquareCover_comp_alternating {n : ℕ} (lam : Nat.Partition n) :
    (evenSquareCover lam).comp (alternatingGroup (Fin n)).subtype =
      Representation.prod
        ((spechtSquare lam).comp (alternatingGroup (Fin n)).subtype)
        ((spechtSquare lam).comp (alternatingGroup (Fin n)).subtype) := by
  change Representation.prod
      ((spechtSquare lam).comp (alternatingGroup (Fin n)).subtype)
      ((signTwist (spechtSquare lam)).comp (alternatingGroup (Fin n)).subtype) = _
  rw [signTwist_comp_alternating]

/-- A nonzero map into a product has a nonzero projection. It is applied after the
simple A_n source has been embedded into the product. -/
theorem nonzero_projection {G V W : Type} [Monoid G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (f : Representation.IntertwiningMap σ (ρ.prod ρ)) (hf : f ≠ 0) :
    ∃ p : Representation.IntertwiningMap σ ρ, p ≠ 0 := by
  let p := (Representation.IntertwiningMap.fst ℂ ρ ρ).comp f
  let q := (Representation.IntertwiningMap.snd ℂ ρ ρ).comp f
  by_cases hp : p = 0
  · refine ⟨q, fun hq => hf ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    apply Prod.ext
    · have hh := congrArg (fun t => t w) hp
      exact hh
    · have hh := congrArg (fun t => t w) hq
      exact hh
  · exact ⟨p, hp⟩

/-- Every simple A_n source maps nontrivially into the witness square. -/
theorem nonzero_into_restricted_square_of_cover_residues {n : ℕ}
    (lam : Nat.Partition n) (modulus : ℤ)
    (hE : ∀ nu : Nat.Partition n, evenCoverNumerator lam nu % modulus ≠ 0)
    (A : FDRep ℂ (alternatingGroup (Fin n))) [Simple A] :
    ∃ f : Representation.IntertwiningMap A.ρ
        ((spechtSquare lam).comp (alternatingGroup (Fin n)).subtype), f ≠ 0 := by
  obtain ⟨nu, h, hh⟩ := exists_nonzero_hom_restrictedSpecht A
  obtain ⟨f, hf, _⟩ := whole_specht_embedding_of_cover_residue lam nu modulus (hE nu)
  let h' : Representation.IntertwiningMap A.ρ (restrictedSpecht nu).ρ :=
    ⟨h.hom.hom.hom, FDRep.hom_hom_hom_comm h⟩
  have hh' : h' ≠ 0 := by
    intro hz
    apply hh
    ext x
    exact congrArg (fun t : Representation.IntertwiningMap A.ρ
      (restrictedSpecht nu).ρ => t x) hz
  let f' : Representation.IntertwiningMap (restrictedSpecht nu).ρ
      ((evenSquareCover lam).comp (alternatingGroup (Fin n)).subtype) :=
    ⟨f.toLinearMap, fun g => f.isIntertwining' g.val⟩
  have hf' : Function.Injective f' := by
    change Function.Injective f
    exact hf
  have hcomp : f'.comp h' ≠ 0 := by
    intro hz
    apply hh'
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change h' x = 0
    apply hf'
    have hhx : f' (h' x) = 0 :=
      congrArg (fun t : Representation.IntertwiningMap A.ρ
        ((evenSquareCover lam).comp (alternatingGroup (Fin n)).subtype) => t x) hz
    exact hhx.trans (map_zero f').symm
  let rho := (spechtSquare lam).comp (alternatingGroup (Fin n)).subtype
  let F : Representation.IntertwiningMap A.ρ (Representation.prod rho rho) :=
    ⟨(f'.comp h').toLinearMap, fun g => by
      change (f'.comp h').toLinearMap ∘ₗ A.ρ g =
        (Representation.prod rho rho) g ∘ₗ (f'.comp h').toLinearMap
      rw [← evenSquareCover_comp_alternating lam]
      exact (f'.comp h').isIntertwining' g⟩
  have hF : F ≠ 0 := by
    intro hz
    apply hcomp
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hhx := congrArg (fun t : Representation.IntertwiningMap A.ρ
      (Representation.prod rho rho) => t x) hz
    exact hhx
  exact nonzero_projection rho A.ρ F hF

/-- From the arithmetic conditions to the HSTZ covering statement. The hypotheses are
`evenNormNumerator lam = n!` and a nonzero residue of `evenCoverNumerator lam nu` for
every partition `nu` of `n`. -/
theorem tensorSquareCovering_of_even_moments {n : ℕ} (hn : 2 ≤ n)
    (lam : Nat.Partition n) (modulus : ℤ)
    (hD : evenNormNumerator lam = (n.factorial : ℤ))
    (hE : ∀ nu : Nat.Partition n, evenCoverNumerator lam nu % modulus ≠ 0) :
    HSTZ.TensorSquareCovering n := by
  haveI : Simple (restrictedSpecht lam) :=
    simple_restrictedSpecht_of_evenNormNumerator hn lam hD
  haveI : Representation.IsIrreducible (restrictedSpecht lam).ρ :=
    FDRep.isIrreducible_of_simple _
  refine ⟨ModuleCat.of ℂ (restrictedSpecht lam), (restrictedSpecht lam).ρ,
    inferInstance, ?_⟩
  intro W _ _ sigma _
  haveI : FiniteDimensional ℂ W :=
    Representation.IsIrreducible.finiteDimensional (ρ := sigma) inferInstance
  let A := FDRep.of sigma
  haveI : Representation.IsIrreducible A.ρ := by
    change Representation.IsIrreducible sigma
    infer_instance
  haveI : Simple A := FDRep.simple_of_isIrreducible A
  obtain ⟨f, hf⟩ := nonzero_into_restricted_square_of_cover_residues lam modulus hE A
  exact ⟨f, hf⟩

/-- The covering statement for n = 5, from the witness (3,2) and all seven partitions
of five; this includes the split constituents of A_5. -/
theorem tensorSquareCovering_five : HSTZ.TensorSquareCovering 5 := by
  exact tensorSquareCovering_of_even_moments (by decide) witness5 1000000007
    degree_five_norm degree_five_cover_residue

end
end HSTZ.TauCetiFinite

#print axioms HSTZ.TauCetiFinite.exists_nonzero_hom_restrictedSpecht
#print axioms HSTZ.TauCetiFinite.nonzero_into_restricted_square_of_cover_residues
#print axioms HSTZ.TauCetiFinite.tensorSquareCovering_of_even_moments
#print axioms HSTZ.TauCetiFinite.tensorSquareCovering_five
