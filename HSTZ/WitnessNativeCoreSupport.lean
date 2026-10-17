import HSTZ.WitnessNativeCore
import HSTZ.StaircaseUniversality

/-! Transfers staircase cyclic universality to the embedded core of the asymmetric
witness, and substitutes the native core generator in the filtered identity. Path and
attachment support are not addressed here. Uses declarations from OpenAI's `math`
repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
open OAI.Saxl

/-- Every Specht module of core degree embeds in the embedded-core cyclic space.
No universality hypothesis is needed; it comes from
`staircase_universal_embedding`. -/
theorem witness_core_universal_embedding (k b delta : ℕ) (hk : 5 ≤ k)
    (mu : YoungDiagram) (t : Tableau (staircase (k-2)).card mu) :
    ∃ E : Representation.IntertwiningMap (spechtRep t)
      (witnessCoreCyclic k b delta hk).toRepresentation, Function.Injective E := by
  obtain ⟨E,hE⟩ := staircase_universal_embedding (k-2) mu t
  exact ⟨(witnessNativeCoreCyclicMap k b delta hk).comp E,
    (witnessNativeCoreCyclicMap_bijective k b delta hk).1.comp hE⟩

theorem witness_filtered_native_core_factor (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk t)=
      witnessRotationPhase k b delta hk t •
        positionProduct (witnessBinaryCut k b delta hk t)
          (witnessNativeCoreMap k b delta hk (staircaseWord (k-2)))
          (witnessComplementPairWord k b delta hk t) := by
  rw [witnessNativeCoreMap_generator]
  exact witness_filtered_core_factor k b delta hk t

end HSTZ
#print axioms HSTZ.witness_core_universal_embedding
#print axioms HSTZ.witness_filtered_native_core_factor
