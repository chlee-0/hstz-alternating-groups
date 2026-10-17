import HSTZ.PieriBlock
import HSTZ.StaircaseInducedSupport

/-! Tensor-carrier induction from position blocks to label stabilizers.
Explicit tensor instances avoid expensive typeclass reconciliation. Support for the
smaller core is an explicit embedding hypothesis. -/
namespace HSTZ
open scoped TensorProduct

noncomputable def staircaseTensorReparam (h : ℕ) {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) nu) :=
  @inducedReparam ℂ
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h 2)))
    (staircaseLabelStabilizer h 2) (StaircasePositionGroup (h+2))
    (OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (staircaseLabelBlockEquiv h 2) (staircaseLabelStabilizer h 2).subtype
    (twoBandConstituent h s u)

/-- The quotient generator is unchanged; its type is inferred directly from the
fully instantiated generic formula, avoiding a dependent coercion search. -/
noncomputable def staircaseTensorReparam_mk (h : ℕ) {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) nu)
    (g : StaircasePositionGroup (h+2))
    (v : OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u) :=
  @inducedReparam_mk ℂ
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h 2)))
    (staircaseLabelStabilizer h 2) (StaircasePositionGroup (h+2))
    (OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (staircaseLabelBlockEquiv h 2) (staircaseLabelStabilizer h 2).subtype
    (twoBandConstituent h s u) g v

theorem staircaseTensorReparam_bijective (h : ℕ) {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) nu) :
    Function.Bijective (staircaseTensorReparam h s u).toLinearMap :=
  @inducedReparam_bijective ℂ
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h 2)))
    (staircaseLabelStabilizer h 2) (StaircasePositionGroup (h+2))
    (OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (staircaseLabelBlockEquiv h 2) (staircaseLabelStabilizer h 2).subtype
    (twoBandConstituent h s u)

/-- Independent core/band induction embeds in the prescribed staircase cyclic
space, conditional on an embedding for the smaller core. -/
theorem staircase_twoBand_block_induced_embedding (h : ℕ) (hh : 1 ≤ h)
    {nu xi : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card nu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) xi) (hxi : xi.colLen 0 ≤ 4)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep s)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ E : Representation.IntertwiningMap
      (Representation.ind (A := OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
        (sumPermHom (OAI.Saxl.cutPositions h 2))
        (independentTensor (OAI.Saxl.spechtRep s) (OAI.Saxl.spechtRep u)))
      (OAI.Saxl.staircaseCyclic (h+2)).toRepresentation, Function.Injective E := by
  let e := staircaseLabelBlockEquiv h 2
  let phi := (staircaseLabelStabilizer h 2).subtype
  let rho := twoBandConstituent h s u
  have hphi : phi.comp e.toMonoidHom = sumPermHom (OAI.Saxl.cutPositions h 2) := by
    apply MonoidHom.ext
    intro g
    exact staircaseLabelBlockEquiv_val h 2 g
  have hrho : rho.comp e.toMonoidHom =
      independentTensor (OAI.Saxl.spechtRep s) (OAI.Saxl.spechtRep u) := by
    ext g x
    simp [rho, twoBandConstituent, e, MonoidHom.comp_apply]
  have hm : ∃ M : Representation.IntertwiningMap
      (Representation.ind (A := OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
        (sumPermHom (OAI.Saxl.cutPositions h 2))
        (independentTensor (OAI.Saxl.spechtRep s) (OAI.Saxl.spechtRep u)))
      (Representation.ind (A := OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u) phi rho),
      Function.Injective M := by
    rw [← hphi, ← hrho]
    exact ⟨staircaseTensorReparam h s u, (staircaseTensorReparam_bijective h s u).1⟩
  obtain ⟨M, hM⟩ := hm
  obtain ⟨N, hN⟩ := staircase_twoBand_native_embedding h hh s u hxi f hf
  exact ⟨N.comp M, hN.comp hM⟩

end HSTZ
#check HSTZ.staircaseTensorReparam_mk
#print axioms HSTZ.staircaseTensorReparam_mk
#print axioms HSTZ.staircaseTensorReparam_bijective
#print axioms HSTZ.staircase_twoBand_block_induced_embedding
