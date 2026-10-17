import HSTZ.IntertwiningCompat
import HSTZ.BandPath
import OAI.RepresentationTheory.Saxl.BandPairing

/-! Connect the native signed path coefficients to HSTZ cyclic spaces.
Nonvanishing of the relevant contraction is a hypothesis of these results, not
proved here. -/
namespace HSTZ
open scoped TensorProduct

theorem pathPairWord_eq_signed (r : ℕ) :
    pathPairWord r = ((-1 : ℂ)^r) • OAI.Saxl.Path.bandWord r := by
  funext w
  change OAI.Saxl.wordTensor _ 2 2 (_ ⊗ₜ[ℂ] _) w = _
  rw [OAI.Saxl.wordTensor_tmul]
  exact OAI.Saxl.PathLayer.paired_rowAlt r w

/-- Nonzero scalar rescaling preserves the prescribed-vector orbit span. -/
theorem cyclicSpan_smul_nonzero {K G V : Type*} [Field K] [Monoid G]
    [AddCommGroup V] [Module K V] (rho : Representation K G V)
    (c : K) (hc : c ≠ 0) (v : V) : cyclicSpan rho (c • v) = cyclicSpan rho v := by
  apply le_antisymm
  · exact (cyclicSpan_le_iff rho (c • v) (cyclicSubrepresentation rho v)).mpr
      ((cyclicSpan rho v).smul_mem c (generator_mem_cyclicSpan rho v))
  · apply (cyclicSpan_le_iff rho v (cyclicSubrepresentation rho (c • v))).mpr
    change v ∈ cyclicSpan rho (c • v)
    have h := (cyclicSpan rho (c • v)).smul_mem c⁻¹
      (generator_mem_cyclicSpan rho (c • v))
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using h

theorem pathPairWord_cyclic_eq (r : ℕ) :
    cyclicSpan (OAI.Saxl.wordRep _ 4) (pathPairWord r) =
      cyclicSpan (OAI.Saxl.wordRep _ 4) (OAI.Saxl.Path.bandWord r) := by
  rw [pathPairWord_eq_signed]
  exact cyclicSpan_smul_nonzero _ _ (pow_ne_zero r (by norm_num)) _

theorem pathPairWord_real (r : ℕ) : star (pathPairWord r) = pathPairWord r := by
  rw [pathPairWord_eq_signed]
  simp only [star_smul,star_pow,star_neg,star_one,OAI.Saxl.Path.bandWord_real]

theorem bandPath_native_generator (h : ℕ) :
    ((-1 : ℂ)^(h+1)) • bandPathMap h (OAI.Saxl.Path.bandWord (h+1)) =
      bandPairWord h 2 := by
  have he := bandPathMap_generator h
  rw [pathPairWord_eq_signed] at he
  change (bandPathMap h).toLinearMap (_ • _) = _ at he
  rw [map_smul] at he
  exact he

theorem bandPath_native_cyclic_image (h : ℕ) :
    (cyclicSpan (OAI.Saxl.wordRep _ 4) (OAI.Saxl.Path.bandWord (h+1))).map
      (bandPathMap h).toLinearMap =
      cyclicSpan (OAI.Saxl.wordRep _ _) (bandPairWord h 2) := by
  rw [← pathPairWord_cyclic_eq]
  exact bandPath_cyclic_image h

/-- A nonzero contraction with the real path word gives a Specht embedding.
Nonvanishing of that contraction is a hypothesis. -/
theorem pathPairWord_contraction_embedding (r : ℕ) {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau (2*r+1) mu)
    (x : (OAI.Saxl.spechtSub t).toSubmodule)
    (L : Fin (mu.colLen 0) → Fin 4 → ℂ)
    (hnz : dotProduct (OAI.Saxl.wordMap L x.val) (pathPairWord r) ≠ 0) :
    ∃ F : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (OAI.Saxl.cyclic (OAI.Saxl.wordRep _ 4) (pathPairWord r)).toRepresentation,
      Function.Injective F := by
  obtain ⟨F,hF⟩ := OAI.Saxl.hom_to_cyclic_of_pair L (OAI.Saxl.spechtSub t)
    x (pathPairWord r) (pathPairWord_real r) hnz
  change Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
    (OAI.Saxl.cyclic (OAI.Saxl.wordRep _ 4) (pathPairWord r)).toRepresentation at F
  letI := OAI.Saxl.specht_irreducible t
  exact ⟨F,(Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

/-- The band representation pulled back along the position-group isomorphism. -/
noncomputable def pathBandRepresentation (h : ℕ) :=
  (OAI.Saxl.wordRep (OAI.Saxl.bandSize h 2)
    ((OAI.Saxl.staircase (h+2)).colLen 0 * (OAI.Saxl.staircase (h+2)).colLen 0)).comp
      (positionPermHom (OAI.Saxl.bandPathEquiv h))

/-- Cyclic restriction with the target generating vector named explicitly. -/
noncomputable def bandPathCyclicMap (h : ℕ) : Representation.IntertwiningMap
    (cyclicSubrepresentation (OAI.Saxl.wordRep (2*(h+1)+1) 4)
      (pathPairWord (h+1))).toRepresentation
    (cyclicSubrepresentation (pathBandRepresentation h) (bandPairWord h 2)).toRepresentation where
  toLinearMap :=
    { toFun := fun x => ⟨bandPathMap h x.val, by
        have hx := cyclicSpan_apply_mem (bandPathMap h) (pathPairWord (h+1)) x.property
        rw [bandPathMap_generator] at hx
        exact hx⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (bandPathMap h).toLinearMap.map_add x.val y.val
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (bandPathMap h).toLinearMap.map_smul c x.val }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (bandPathMap h).map_action g x.val

theorem bandPathCyclicMap_injective (h : ℕ) : Function.Injective (bandPathCyclicMap h) := by
  intro x y he
  apply Subtype.ext
  apply bandPathMap_injective h
  exact congrArg Subtype.val he

/-- A nonzero contraction (a hypothesis) embeds the Specht module in the
band cyclic space after the explicitly stated change of position group. -/
theorem bandPath_contraction_embedding (h : ℕ) {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau (2*(h+1)+1) mu)
    (x : (OAI.Saxl.spechtSub t).toSubmodule)
    (L : Fin (mu.colLen 0) → Fin 4 → ℂ)
    (hnz : dotProduct (OAI.Saxl.wordMap L x.val) (pathPairWord (h+1)) ≠ 0) :
    ∃ F : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (pathBandRepresentation h) (bandPairWord h 2)).toRepresentation,
      Function.Injective F := by
  obtain ⟨F,hF⟩ := pathPairWord_contraction_embedding (h+1) t x L hnz
  exact ⟨(bandPathCyclicMap h).comp F,(bandPathCyclicMap_injective h).comp hF⟩

end HSTZ
#print axioms HSTZ.pathPairWord_eq_signed
#print axioms HSTZ.cyclicSpan_smul_nonzero
#print axioms HSTZ.pathPairWord_cyclic_eq
#print axioms HSTZ.pathPairWord_real
#print axioms HSTZ.bandPath_native_generator
#print axioms HSTZ.bandPath_native_cyclic_image
#print axioms HSTZ.pathPairWord_contraction_embedding
#print axioms HSTZ.bandPathCyclicMap
#print axioms HSTZ.bandPathCyclicMap_injective
#print axioms HSTZ.bandPath_contraction_embedding
