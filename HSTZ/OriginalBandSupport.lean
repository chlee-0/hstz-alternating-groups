import HSTZ.FourRowSupport
import OAI.RepresentationTheory.Saxl.CyclicSector

/-! Four-row embeddings under the original band position group.
The only support input is the local four-row path theorem. -/
namespace HSTZ

/-- Injective letter transport gives support before position reindexing. -/
theorem liftedPath_support (h : ℕ) (hh : 1 ≤ h) (mu : YoungDiagram)
    (t : OAI.Saxl.Tableau (2*(h+1)+1) mu) (hmu : mu.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (OAI.Saxl.cyclic (OAI.Saxl.wordRep _ _)
        (encodedLetterLift (OAI.Saxl.lowLetter h) (OAI.Saxl.lowLetter h)
          (pathPairWord (h+1)))).toRepresentation, F ≠ 0 := by
  obtain ⟨f, hf⟩ := fourRow_pathPair_embedding (h+1) (by omega) t hmu
  let phi := encodedLetterLift (n := 2*(h+1)+1)
    (OAI.Saxl.lowLetter h) (OAI.Saxl.lowLetter h)
  let F := (cyclicImageMap phi (pathPairWord (h+1))).comp f
  refine ⟨F, ?_⟩
  have hphi : Function.Injective phi := encodedLetterLift_injective _ _
    (OAI.Saxl.lowLetter_injective h) (OAI.Saxl.lowLetter_injective h)
  have hi : Function.Injective (cyclicImageMap phi (pathPairWord (h+1))) := by
    intro x y he
    apply Subtype.ext
    exact hphi (congrArg Subtype.val he)
  have hF : Function.Injective F := hi.comp hf
  intro hz
  let x : OAI.Saxl.Specht t :=
    ⟨OAI.Saxl.polytabloid t, OAI.Saxl.mem_cyclic _ _⟩
  have he : F x = F 0 := by rw [hz]; rfl
  have hx := congrArg Subtype.val (hF he)
  exact OAI.Saxl.polytabloid_ne_zero t hx

/-- Four-row support under the original band position group/tableau size. -/
theorem originalBand_support (h : ℕ) (hh : 1 ≤ h) (mu : YoungDiagram)
    (t : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) mu) (hmu : mu.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (OAI.Saxl.cyclic (OAI.Saxl.wordRep _ _) (bandPairWord h 2)).toRepresentation,
      F ≠ 0 := by
  have hs := OAI.Saxl.support_relabel (OAI.Saxl.bandPathEquiv h)
    (encodedLetterLift (OAI.Saxl.lowLetter h) (OAI.Saxl.lowLetter h)
      (pathPairWord (h+1))) (liftedPath_support h hh) mu t hmu
  have he : (fun w =>
      encodedLetterLift (OAI.Saxl.lowLetter h) (OAI.Saxl.lowLetter h)
        (pathPairWord (h+1)) (w ∘ OAI.Saxl.bandPathEquiv h)) = bandPairWord h 2 :=
    bandPathMap_generator h
  rw [he] at hs
  exact hs

/-- An embedding for the original group itself, rather than a dimension or support predicate. -/
theorem originalBand_embedding (h : ℕ) (hh : 1 ≤ h) (mu : YoungDiagram)
    (t : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 2) mu) (hmu : mu.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (bandPairWord h 2)).toRepresentation,
      Function.Injective F := by
  obtain ⟨F, hF⟩ := originalBand_support h hh mu t hmu
  letI := OAI.Saxl.specht_irreducible t
  exact ⟨F,(Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

end HSTZ
#print axioms HSTZ.liftedPath_support
#print axioms HSTZ.originalBand_support
#print axioms HSTZ.originalBand_embedding
