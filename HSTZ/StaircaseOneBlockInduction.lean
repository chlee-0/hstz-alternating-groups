import HSTZ.StaircaseOneTensorCarrier
import HSTZ.OneBandNativeSupport

/-! One-step block-induced tensor support. Support for the smaller core remains a hypothesis. -/
namespace HSTZ
open scoped TensorProduct

/-- Independent core/band induction embeds in the prescribed native staircase cyclic
space, assuming an embedding for the smaller core. -/
theorem staircase_oneBand_block_induced_embedding (h : ℕ)
    {nu xi : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card nu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) xi) (hxi : xi.colLen 0 ≤ 1)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep s)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ E : Representation.IntertwiningMap
      (Representation.ind (A := OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
        (sumPermHom (OAI.Saxl.cutPositions h 1))
        (independentTensor (OAI.Saxl.spechtRep s) (OAI.Saxl.spechtRep u)))
      (OAI.Saxl.staircaseCyclic (h+1)).toRepresentation, Function.Injective E := by
  let e := staircaseLabelBlockEquiv h 1
  let phi := (staircaseLabelStabilizer h 1).subtype
  let rho := oneTensorLabelAction h s u
  have hphi : phi.comp e.toMonoidHom = sumPermHom (OAI.Saxl.cutPositions h 1) := by
    apply MonoidHom.ext
    intro g
    exact staircaseLabelBlockEquiv_val h 1 g
  have hrho : rho.comp e.toMonoidHom =
      independentTensor (OAI.Saxl.spechtRep s) (OAI.Saxl.spechtRep u) := by
    ext g x
    simp [rho, oneTensorLabelAction, oneBandConstituent, e, MonoidHom.comp_apply]
  have hm : ∃ M : Representation.IntertwiningMap
      (Representation.ind (A := OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
        (sumPermHom (OAI.Saxl.cutPositions h 1))
        (independentTensor (OAI.Saxl.spechtRep s) (OAI.Saxl.spechtRep u)))
      (Representation.ind (A := OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u) phi rho),
      Function.Injective M := by
    rw [← hphi, ← hrho]
    exact ⟨staircaseOneTensorReparam h s u, (staircaseOneTensorReparam_bijective h s u).1⟩
  obtain ⟨M, hM⟩ := hm
  let N := staircaseOneBandNativeMap h s u hxi f hf
  have hN : Function.Injective N.toLinearMap :=
    staircaseOneBandNativeMap_injective h s u hxi f hf
  exact ⟨N.comp M, hN.comp hM⟩

end HSTZ
#print axioms HSTZ.staircase_oneBand_block_induced_embedding
