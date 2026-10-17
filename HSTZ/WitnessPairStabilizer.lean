import HSTZ.IntertwiningCompat
import HSTZ.WitnessPairSector
import HSTZ.FactorSupport

/-! The original block carrier in the pair-word stabilizer space.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The phase changes a generator, not its cyclic carrier. No Young alignment is
asserted. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section Carrier
variable (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
  (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessPairStabilizerRepresentation :=
  stabilizerRepresentation (witnessPairRep k b delta hk (n := n))
    (labelOrbitBase (Equiv.Perm (Fin n)) (witnessCorePairLabel k b delta hk z))
    (witnessPairCut k b delta hk z)

def witnessPairStabilizerEncoder := pullbackIntertwiner
  (encodedPairModelIntertwiner n ((witnessDiagram k b delta hk).transpose.colLen 0)
    ((witnessDiagram k b delta hk).colLen 0))
  (witnessPairLabelStabilizer k b delta hk z).subtype

/-- The original block carrier itself, not merely a constituent or a dimension
equality. -/
theorem witnessPairStabilizer_image :
    (stabilizerCyclic (witnessPairRep k b delta hk (n := n))
      (labelOrbitBase (Equiv.Perm (Fin n)) (witnessCorePairLabel k b delta hk z))
      (witnessPairCut k b delta hk z)).map (encodedPairModelEquiv n _ _).toLinearMap =
      (witnessCoreComplementBlockCyclic k b delta hk z).toSubmodule := by
  have hi := cyclicSpan_image (witnessPairStabilizerEncoder k b delta hk z)
    (witnessPairCut k b delta hk z)
  change (stabilizerCyclic _ _ (witnessPairCut k b delta hk z)).map
      (encodedPairModelEquiv n _ _).toLinearMap =
    cyclicSpan ((wordRep n _).comp (witnessPairLabelStabilizer k b delta hk z).subtype)
      (encodedPairModelEquiv n _ _ (witnessPairCut k b delta hk z)) at hi
  rw [encodedPair_witnessCut,witnessPairLabelStabilizer_eq,
    ← witnessCorePosition_sectorGroup_eq,← blockSpan_eq_sectorSpan,
    witness_filtered_core_factor,cyclicSpan_smul_nonzero _ _
      (witnessRotationPhase_ne_zero k b delta hk z)] at hi
  change _ = cyclicSpan _ ((positionTensorIntertwiner (witnessBinaryCut k b delta hk z))
    (witnessEmbeddedCorePair k b delta hk ⊗ₜ[ℂ] witnessComplementPairWord k b delta hk z))
  have hgen : (positionTensorIntertwiner (witnessBinaryCut k b delta hk z))
      (witnessEmbeddedCorePair k b delta hk ⊗ₜ[ℂ] witnessComplementPairWord k b delta hk z) =
      witnessCoreComplementProduct k b delta hk z := positionTensor_tmul _ _ _
  rw [hgen]
  exact hi

def witnessBlockPairInverse := pullbackIntertwiner
  (encodedPairModelInverse n ((witnessDiagram k b delta hk).transpose.colLen 0)
    ((witnessDiagram k b delta hk).colLen 0)) (sumPermHom (witnessBinaryCut k b delta hk z))

theorem witnessBlockPairInverse_mem (x : witnessCoreComplementBlockCyclic k b delta hk z) :
    witnessBlockPairInverse k b delta hk z x.val ∈ stabilizerCyclic
      (witnessPairRep k b delta hk (n := n))
      (labelOrbitBase (Equiv.Perm (Fin n)) (witnessCorePairLabel k b delta hk z))
      (witnessPairCut k b delta hk z) := by
  have hx := x.property
  change x.val∈(witnessCoreComplementBlockCyclic k b delta hk z).toSubmodule at hx
  rw [← witnessPairStabilizer_image k b delta hk z] at hx
  obtain ⟨y,hy,hey⟩ := Submodule.mem_map.mp hx
  have he : witnessBlockPairInverse k b delta hk z x.val = y := by
    change (encodedPairModelEquiv n _ _).symm x.val = y
    rw [← hey]
    exact (encodedPairModelEquiv n _ _).symm_apply_apply y
  rw [he]
  exact hy

def witnessBlockToPairStabilizer : Representation.IntertwiningMap
    (witnessCoreComplementBlockCyclic k b delta hk z).toRepresentation
    ((witnessPairStabilizerRepresentation k b delta hk z).comp
      (witnessPairLabelBlockEquiv k b delta hk z).toMonoidHom) where
  toLinearMap := ((witnessBlockPairInverse k b delta hk z).toLinearMap.comp
    (witnessCoreComplementBlockCyclic k b delta hk z).toSubmodule.subtype).codRestrict _
      (witnessBlockPairInverse_mem k b delta hk z)
  isIntertwining' gh := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessBlockPairInverse k b delta hk z).map_action gh x.val

theorem witnessBlockToPairStabilizer_injective :
    Function.Injective (witnessBlockToPairStabilizer k b delta hk z) := by
  intro x y he
  apply Subtype.ext
  exact (encodedPairModelEquiv n _ _).symm.injective (congrArg Subtype.val he)
end Carrier

/-- Both original factor Specht modules enter the ordinary-induction base.
The product group and stabilizer action are related by the equivalence. -/
theorem containedWitness_pair_stabilizer_embedding
    {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta) (hzero : ∀ c, t ≤ c → e c = 0)
    (mu : YoungDiagram) (u : Tableau (staircase (k-2)).card mu)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (hpi : (containedPath h hh d (witnessPathSize k) m).colLen 0≤4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0≤4) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap
      ((independentTensor (spechtRep u) (spechtRep s)).comp
        (witnessPairLabelBlockEquiv k b delta hp.staircase_bound z).symm.toMonoidHom)
      (witnessPairStabilizerRepresentation k b delta hp.staircase_bound z),
      Function.Injective F := by
  obtain ⟨F,hF⟩ := containedWitness_core_complement_block_embedding hh he k b delta hp
    htm hroom hclear hcapacity hsize hzero mu u s hpi hc hE z
  let J := (witnessBlockToPairStabilizer k b delta hp.staircase_bound z).comp F
  exact ⟨transportIntertwiner (witnessPairLabelBlockEquiv k b delta hp.staircase_bound z) J,
    (witnessBlockToPairStabilizer_injective k b delta hp.staircase_bound z).comp hF⟩
end
end HSTZ
#print axioms HSTZ.witnessPairStabilizer_image
#print axioms HSTZ.witnessBlockPairInverse_mem
#print axioms HSTZ.witnessBlockToPairStabilizer_injective
#print axioms HSTZ.containedWitness_pair_stabilizer_embedding
