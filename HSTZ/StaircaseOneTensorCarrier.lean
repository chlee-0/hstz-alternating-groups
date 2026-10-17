import HSTZ.InducedReparam
import HSTZ.StaircaseOneBandStabilizer

/-! One-step tensor induction carriers and generators on the native HSTZ/OpenAI spaces.
The ambient permutation and the inverse/right action are unchanged. -/
namespace HSTZ
open scoped TensorProduct
/-- Named action of the label stabilizer on the two Specht factors. -/
noncomputable def oneTensorLabelAction (h : ℕ) {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) :
    Representation ℂ (staircaseLabelStabilizer h 1)
      (OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u) :=
  oneBandConstituent h s u

noncomputable def staircaseOneTensorReparam (h : ℕ) {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) :=
  @inducedReparam ℂ
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h 1)))
    (staircaseLabelStabilizer h 1) (Equiv.Perm (Fin (OAI.Saxl.staircase (h+1)).card))
    (OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (staircaseLabelBlockEquiv h 1) (staircaseLabelStabilizer h 1).subtype
    (oneTensorLabelAction h s u)

/-- The quotient generator is unchanged; the type is inferred directly from the fully
instantiated generic formula, avoiding dependent coercion search. -/
noncomputable def staircaseOneTensorReparam_mk (h : ℕ) {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu)
    (g : Equiv.Perm (Fin (OAI.Saxl.staircase (h+1)).card))
    (v : OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u) :=
  @inducedReparam_mk ℂ
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h 1)))
    (staircaseLabelStabilizer h 1) (Equiv.Perm (Fin (OAI.Saxl.staircase (h+1)).card))
    (OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (staircaseLabelBlockEquiv h 1) (staircaseLabelStabilizer h 1).subtype
    (oneTensorLabelAction h s u) g v

theorem staircaseOneTensorReparam_bijective (h : ℕ) {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) :
    Function.Bijective (staircaseOneTensorReparam h s u).toLinearMap :=
  @inducedReparam_bijective ℂ
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h 1)))
    (staircaseLabelStabilizer h 1) (Equiv.Perm (Fin (OAI.Saxl.staircase (h+1)).card))
    (OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (staircaseLabelBlockEquiv h 1) (staircaseLabelStabilizer h 1).subtype
    (oneTensorLabelAction h s u)

noncomputable def staircaseOneTensorReparamInverse (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) :=
  @inducedReparamInverse ℂ
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h 1)))
    (staircaseLabelStabilizer h 1) (Equiv.Perm (Fin (OAI.Saxl.staircase (h+1)).card))
    (OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (staircaseLabelBlockEquiv h 1) (staircaseLabelStabilizer h 1).subtype
    (oneBandConstituent h t u)

noncomputable def staircaseOneTensorReparam_leftInverse (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) :=
  @inducedReparam_leftInverse ℂ
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h 1)))
    (staircaseLabelStabilizer h 1) (Equiv.Perm (Fin (OAI.Saxl.staircase (h+1)).card))
    (OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (staircaseLabelBlockEquiv h 1) (staircaseLabelStabilizer h 1).subtype
    (oneBandConstituent h t u)

noncomputable def staircaseOneTensorReparam_rightInverse (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) :=
  @inducedReparam_rightInverse ℂ
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h 1)))
    (staircaseLabelStabilizer h 1) (Equiv.Perm (Fin (OAI.Saxl.staircase (h+1)).card))
    (OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (staircaseLabelBlockEquiv h 1) (staircaseLabelStabilizer h 1).subtype
    (oneBandConstituent h t u)

end HSTZ
#check HSTZ.staircaseOneTensorReparam_mk
#check HSTZ.staircaseOneTensorReparam_leftInverse
#check HSTZ.staircaseOneTensorReparam_rightInverse
#print axioms HSTZ.staircaseOneTensorReparam_mk
#print axioms HSTZ.staircaseOneTensorReparam_bijective
#print axioms HSTZ.staircaseOneTensorReparam_leftInverse
#print axioms HSTZ.staircaseOneTensorReparam_rightInverse
