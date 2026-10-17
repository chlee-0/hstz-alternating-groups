import HSTZ.FinsuppAction
import HSTZ.StaircaseFilter

/-! A coefficient-preserving embedding of the paired-word staircase cyclic space
into the native staircase cyclic space, used for one- and two-step staircase
support. -/
namespace HSTZ
/-- Coefficient-preserving embedding of the paired-word cyclic space into the
native staircase cyclic space. -/
theorem staircase_native_cyclic_embedding (m : ℕ) :
    ∃ E : Representation.IntertwiningMap
      (cyclicSubrepresentation (finsuppAction ℂ (Equiv.Perm (Fin (OAI.Saxl.staircase m).card)) _)
        (staircasePairGenerator m)).toRepresentation
      (OAI.Saxl.staircaseCyclic m).toRepresentation, Function.Injective E := by
  let enc := encodedPairModelIntertwiner (OAI.Saxl.staircase m).card
    ((OAI.Saxl.staircase m).colLen 0) ((OAI.Saxl.staircase m).colLen 0)
  let M := cyclicImageMap enc (staircasePairGenerator m)
  have hM : Function.Injective M := by
    intro x y he
    apply Subtype.ext
    exact (encodedPairModelIntertwiner_bijective _ _ _).1 (congrArg Subtype.val he)
  have he : enc (staircasePairGenerator m) = OAI.Saxl.staircaseWord m :=
    encodedPair_staircaseGenerator m
  have hE : ∃ E : Representation.IntertwiningMap
      (cyclicSubrepresentation (finsuppAction ℂ (Equiv.Perm (Fin (OAI.Saxl.staircase m).card)) _)
        (staircasePairGenerator m)).toRepresentation
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _)
        (enc (staircasePairGenerator m))).toRepresentation,
      Function.Injective E := ⟨M, hM⟩
  rw [he] at hE
  exact hE

end HSTZ
#print axioms HSTZ.staircase_native_cyclic_embedding
