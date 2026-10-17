import HSTZ.FinsuppAction
import HSTZ.IntertwiningCompat
import HSTZ.OriginalBandSupport

/-! Constituent embeddings into the selected staircase induction base.
The smaller-staircase embedding is an explicit hypothesis, not a universality statement. -/
namespace HSTZ

/-- Injectively transport a supplied constituent of the prescribed smaller core. -/
theorem shiftedCore_embedding (h s : ℕ) {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ F : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s)).toRepresentation,
      Function.Injective F := by
  let phi := shiftedCoreMap h s
  have hi : Function.Injective (cyclicImageMap phi (OAI.Saxl.staircaseWord h)) := by
    intro x y he
    apply Subtype.ext
    exact shiftedCoreMap_injective h s (congrArg Subtype.val he)
  have hF : Function.Injective
      ((cyclicImageMap phi (OAI.Saxl.staircaseWord h)).comp f) := hi.comp hf
  have he : phi (OAI.Saxl.staircaseWord h) = shiftedCoreWord h s :=
    shiftedCoreMap_generator h s
  exact he ▸ ⟨(cyclicImageMap phi (OAI.Saxl.staircaseWord h)).comp f, hF⟩

/-- The ordinary-induction base, pulled back along its product-block isomorphism.
No change of group for the induced carrier is hidden in this abbreviation. -/
noncomputable abbrev staircaseBaseRepresentation (h s : ℕ) :=
  ((cyclicSubrepresentation
    ((finsuppAction ℂ
      (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card)) _).comp
      (staircaseLabelStabilizer h s).subtype) (staircasePairCut h s)).toRepresentation).comp
    (staircaseLabelBlockEquiv h s).toMonoidHom

/-- The independent core/four-row band constituent tensor embeds into the selected-vector
induction base. The smaller-core embedding remains a hypothesis. -/
theorem staircase_twoBand_base_embedding (h : ℕ) (hh : 1 ≤ h)
    {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) nu) (hnu : nu.colLen 0 ≤ 4)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ F : Representation.IntertwiningMap
      (independentTensor (OAI.Saxl.spechtRep t) (OAI.Saxl.spechtRep u))
      (staircaseBaseRepresentation h 2), Function.Injective F := by
  obtain ⟨core, hcore⟩ := shiftedCore_embedding h 2 t f hf
  obtain ⟨band, hband⟩ := originalBand_embedding h hh nu u hnu
  let tensorMap := independentTensorMap core band
  exact ⟨(staircaseFactorToStabilizer h 2).comp tensorMap,
    (staircaseFactorToStabilizer_bijective h 2).1.comp
      (independentTensorMap_injective core band hcore hband)⟩

/-- Move a source action across a group isomorphism, preserving the underlying linear
map and the original target action. -/
def transportIntertwiner {R G H V W : Type*} [CommRing R] [Monoid G] [Monoid H]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    {rho : Representation R G V} {sigma : Representation R H W}
    (e : G ≃* H) (phi : Representation.IntertwiningMap rho (sigma.comp e.toMonoidHom)) :
    Representation.IntertwiningMap (rho.comp e.symm.toMonoidHom) sigma where
  toLinearMap := phi.toLinearMap
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    have he := phi.map_action (e.symm h) v
    change phi (rho (e.symm h) v) = sigma (e (e.symm h)) (phi v) at he
    rw [MulEquiv.apply_symm_apply] at he
    exact he

/-- The stabilizer cyclic representation used by ordinary induction. -/
noncomputable abbrev staircaseStabilizerRepresentation (h s : ℕ) :=
  (cyclicSubrepresentation
    ((finsuppAction ℂ
      (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card)) _).comp
      (staircaseLabelStabilizer h s).subtype) (staircasePairCut h s)).toRepresentation

/-- The same constituent tensor, now acted on by the stabilizer, embeds into the
ordinary-induction source. The group change is explicit. -/
theorem staircase_twoBand_stabilizer_embedding (h : ℕ) (hh : 1 ≤ h)
    {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) nu) (hnu : nu.colLen 0 ≤ 4)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ F : Representation.IntertwiningMap
      ((independentTensor (OAI.Saxl.spechtRep t) (OAI.Saxl.spechtRep u)).comp
        (staircaseLabelBlockEquiv h 2).symm.toMonoidHom)
      (staircaseStabilizerRepresentation h 2), Function.Injective F := by
  obtain ⟨F, hF⟩ := staircase_twoBand_base_embedding h hh t u hnu f hf
  exact ⟨transportIntertwiner (staircaseLabelBlockEquiv h 2) F, hF⟩

end HSTZ
#print axioms HSTZ.shiftedCore_embedding
#print axioms HSTZ.staircase_twoBand_base_embedding
#print axioms HSTZ.transportIntertwiner
#print axioms HSTZ.staircase_twoBand_stabilizer_embedding
