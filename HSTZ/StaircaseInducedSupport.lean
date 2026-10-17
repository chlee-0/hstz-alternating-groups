import HSTZ.FinsuppAction
import HSTZ.FactorSupport
import HSTZ.InducedEmbedding

/-! Induced core/band embedding in the original prescribed staircase cyclic space.
An embedding of the smaller core is a hypothesis throughout. -/
namespace HSTZ
open scoped TensorProduct

abbrev StaircasePositionGroup (m : ℕ) := Equiv.Perm (Fin (OAI.Saxl.staircase m).card)
abbrev StaircasePairSpace (m : ℕ) :=
  PositionWord (Fin (OAI.Saxl.staircase m).card)
    (Fin ((OAI.Saxl.staircase m).colLen 0) × Fin ((OAI.Saxl.staircase m).colLen 0)) →₀ ℂ

noncomputable abbrev staircasePairRepresentation (m : ℕ) :
    Representation ℂ (StaircasePositionGroup m) (StaircasePairSpace m) :=
  finsuppAction ℂ _ _

noncomputable def staircaseCutFilter (h s : ℕ) : Representation.IntertwiningMap
    (staircasePairRepresentation (h+s)) (staircasePairRepresentation (h+s)) :=
  coordinateFilterIntertwiner
    (sameHighWords (OAI.Saxl.staircase (h+s)).card
      ((OAI.Saxl.staircase (h+s)).colLen 0) ((OAI.Saxl.staircase (h+s)).colLen 0) s)
    (sameHighWords_invariant _ _ _ s)

noncomputable def staircaseSectorMap (h s : ℕ) : Representation.IntertwiningMap
    (Representation.ind (staircaseLabelStabilizer h s).subtype
      (staircaseStabilizerRepresentation h s))
    (cyclicSubrepresentation (staircasePairRepresentation (h+s)) (staircasePairCut h s)).toRepresentation :=
  sectorInductionMap (staircasePairRepresentation (h+s))
    (labelOrbitBase (StaircasePositionGroup (h+s)) (staircaseHighLabel h s)) (staircasePairCut h s)

theorem staircaseSectorMap_bijective (h s : ℕ) : Function.Bijective (staircaseSectorMap h s) :=
  staircasePairCut_induction_bijective h s

/-- Induce a base embedding, compose the sector bijection, and lift through the
equivariant filter into the original cyclic space. -/
theorem staircase_induced_embedding_lift (h s : ℕ) {U : Type*}
    [AddCommGroup U] [Module ℂ U]
    (tau : Representation ℂ (staircaseLabelStabilizer h s) U)
    (j : Representation.IntertwiningMap tau (staircaseStabilizerRepresentation h s))
    (hj : Function.Injective j) :
    ∃ i : Representation.IntertwiningMap
      (Representation.ind (staircaseLabelStabilizer h s).subtype tau)
      (cyclicSubrepresentation (staircasePairRepresentation (h+s))
        (staircasePairGenerator (h+s))).toRepresentation,
      Function.Injective i ∧ ∀ u,
        cyclicImageMap (staircaseCutFilter h s) (staircasePairGenerator (h+s)) (i u) =
          staircaseSectorMap h s (inducedMap (staircaseLabelStabilizer h s).subtype j u) := by
  letI : NeZero (Nat.card (staircaseLabelStabilizer h s) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (staircaseLabelStabilizer h s)).ne'⟩
  letI : NeZero (Nat.card (StaircasePositionGroup (h+s)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (StaircasePositionGroup (h+s))).ne'⟩
  let J := (staircaseSectorMap h s).comp
    (inducedMap (staircaseLabelStabilizer h s).subtype j)
  have hJ : Function.Injective J := (staircaseSectorMap_bijective h s).1.comp
    (inducedMap_injective (staircaseLabelStabilizer h s).subtype j hj)
  exact cyclicImage_embedding_lift (staircaseCutFilter h s) (staircasePairGenerator (h+s)) J hJ

/-- The independent Specht tensor, transported to the stabilizer group. -/
noncomputable abbrev twoBandConstituent (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) nu) :
    Representation ℂ (staircaseLabelStabilizer h 2)
      (OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u) :=
  (independentTensor (OAI.Saxl.spechtRep t) (OAI.Saxl.spechtRep u)).comp
    (staircaseLabelBlockEquiv h 2).symm.toMonoidHom

/-- An induced constituent tensor embeds in the original pair-word staircase
cyclic space, conditional on an embedding of its smaller core (a hypothesis). -/
theorem staircase_twoBand_induced_embedding (h : ℕ) (hh : 1 ≤ h)
    {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) nu) (hnu : nu.colLen 0 ≤ 4)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ i : Representation.IntertwiningMap
      (Representation.ind (A := OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u)
        (staircaseLabelStabilizer h 2).subtype (twoBandConstituent h t u))
      (cyclicSubrepresentation (staircasePairRepresentation (h+2))
        (staircasePairGenerator (h+2))).toRepresentation, Function.Injective i := by
  obtain ⟨j, hj⟩ := staircase_twoBand_stabilizer_embedding h hh t u hnu f hf
  obtain ⟨i, hi, _⟩ := staircase_induced_embedding_lift (U := OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u)
    h 2 (twoBandConstituent h t u) j hj
  exact ⟨i, hi⟩

/-- The same induced embedding in the native prescribed `staircaseWord` cyclic
representation, using the coefficient-preserving word encoder. -/
theorem staircase_twoBand_native_embedding (h : ℕ) (hh : 1 ≤ h)
    {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) nu) (hnu : nu.colLen 0 ≤ 4)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ i : Representation.IntertwiningMap
      (Representation.ind (A := OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u)
        (staircaseLabelStabilizer h 2).subtype (twoBandConstituent h t u))
      (OAI.Saxl.staircaseCyclic (h+2)).toRepresentation, Function.Injective i := by
  obtain ⟨i, hi⟩ := staircase_twoBand_induced_embedding h hh t u hnu f hf
  let enc := encodedPairModelIntertwiner (OAI.Saxl.staircase (h+2)).card
    ((OAI.Saxl.staircase (h+2)).colLen 0) ((OAI.Saxl.staircase (h+2)).colLen 0)
  let M := cyclicImageMap enc (staircasePairGenerator (h+2))
  have hM : Function.Injective M := by
    intro x y he
    apply Subtype.ext
    exact (encodedPairModelIntertwiner_bijective _ _ _).1 (congrArg Subtype.val he)
  have he : enc (staircasePairGenerator (h+2)) = OAI.Saxl.staircaseWord (h+2) :=
    encodedPair_staircaseGenerator (h+2)
  have hE : ∃ E : Representation.IntertwiningMap
      (Representation.ind (A := OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u)
        (staircaseLabelStabilizer h 2).subtype (twoBandConstituent h t u))
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (enc (staircasePairGenerator (h+2)))).toRepresentation,
      Function.Injective E := ⟨M.comp i, hM.comp hi⟩
  rw [he] at hE
  exact hE

end HSTZ
#print axioms HSTZ.staircaseSectorMap_bijective
#print axioms HSTZ.staircase_induced_embedding_lift
#print axioms HSTZ.staircase_twoBand_induced_embedding
#print axioms HSTZ.staircase_twoBand_native_embedding
