import HSTZ.WitnessNativeCoreSupport
import HSTZ.ContainedComplementSupport
import HSTZ.PositionBlock

/-! Independent position-product support for the core and the full complement.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The full position cyclic carrier is restricted along the original witness cut.
Sector induction, Young alignment and full witness support are treated separately. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

section Product
variable (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
  (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessCoreComplementProduct :=
  positionProduct (witnessBinaryCut k b delta hk z)
    (witnessEmbeddedCorePair k b delta hk)
    (witnessComplementPairWord k b delta hk z)

abbrev witnessCoreComplementCyclic :=
  cyclic (wordRep n ((witnessDiagram k b delta hk).transpose.colLen 0 *
    (witnessDiagram k b delta hk).colLen 0))
    (witnessCoreComplementProduct k b delta hk z)

abbrev witnessCoreComplementBlockCyclic :=
  cyclicSubrepresentation
    ((wordRep n ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0)).comp
      (sumPermHom (witnessBinaryCut k b delta hk z)))
    ((positionTensorIntertwiner (witnessBinaryCut k b delta hk z))
      (witnessEmbeddedCorePair k b delta hk ⊗ₜ[ℂ] witnessComplementPairWord k b delta hk z))

/-- Every independent-block orbit lies in the span of the full position orbit. -/
theorem witnessCoreComplement_block_le :
    (witnessCoreComplementBlockCyclic k b delta hk z).toSubmodule ≤
      (witnessCoreComplementCyclic k b delta hk z).toSubmodule := by
  change cyclicSpan _ ((positionTensorIntertwiner (witnessBinaryCut k b delta hk z))
    (witnessEmbeddedCorePair k b delta hk ⊗ₜ[ℂ] witnessComplementPairWord k b delta hk z)) ≤ _
  have hg : (positionTensorIntertwiner (witnessBinaryCut k b delta hk z))
      (witnessEmbeddedCorePair k b delta hk ⊗ₜ[ℂ] witnessComplementPairWord k b delta hk z) =
      witnessCoreComplementProduct k b delta hk z := positionTensor_tmul _ _ _
  rw [hg]
  apply Submodule.span_le.mpr
  rintro _ ⟨gh,rfl⟩
  exact Submodule.subset_span ⟨sumPermHom (witnessBinaryCut k b delta hk z) gh,rfl⟩

/-- Inclusion in the full carrier, with the restricted product action. -/
def witnessCoreComplementBlockInclusion : Representation.IntertwiningMap
    (witnessCoreComplementBlockCyclic k b delta hk z).toRepresentation
    ((witnessCoreComplementCyclic k b delta hk z).toRepresentation.comp
      (sumPermHom (witnessBinaryCut k b delta hk z))) where
  toLinearMap := Submodule.inclusion (witnessCoreComplement_block_le k b delta hk z)
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

theorem witnessCoreComplementBlockInclusion_injective :
    Function.Injective (witnessCoreComplementBlockInclusion k b delta hk z) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun w : witnessCoreComplementCyclic k b delta hk z => w.val) h

/-- The inherited bijection specialized to these factors and the original cut. -/
def witnessCoreComplementFactorMap : Representation.IntertwiningMap
    (independentTensor (witnessCoreCyclic k b delta hk).toRepresentation
      (cyclic (wordRep (witnessComplementSize k b delta)
        ((witnessDiagram k b delta hk).transpose.colLen 0 *
          (witnessDiagram k b delta hk).colLen 0))
        (witnessComplementPairWord k b delta hk z)).toRepresentation)
    (witnessCoreComplementBlockCyclic k b delta hk z).toRepresentation :=
  positionFactorMap (witnessBinaryCut k b delta hk z)
      (witnessEmbeddedCorePair k b delta hk) (witnessComplementPairWord k b delta hk z)

theorem witnessCoreComplementFactorMap_bijective :
    Function.Bijective (witnessCoreComplementFactorMap k b delta hk z) :=
  positionFactorMap_bijective (witnessBinaryCut k b delta hk z)
      (witnessEmbeddedCorePair k b delta hk) (witnessComplementPairWord k b delta hk z)

/-- Coordinates are the ordered product of the same full factors. -/
theorem witnessCoreComplementFactorMap_tmul
    (x : witnessCoreCyclic k b delta hk)
    (y : cyclic (wordRep (witnessComplementSize k b delta)
      ((witnessDiagram k b delta hk).transpose.colLen 0 *
        (witnessDiagram k b delta hk).colLen 0))
      (witnessComplementPairWord k b delta hk z)) :
    (witnessCoreComplementFactorMap k b delta hk z (x ⊗ₜ[ℂ] y)).val =
      positionProduct (witnessBinaryCut k b delta hk z) x.val y.val := by
  change positionTensor (witnessBinaryCut k b delta hk z) (x.val ⊗ₜ[ℂ] y.val) = _
  exact positionTensor_tmul _ _ _
end Product

/-- Core universality and support of the full original complement compose into
an injective independent full-group map into the full product carrier.
No sector induction or target Specht identification is asserted. -/
theorem containedWitness_core_complement_block_embedding
    {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta) (hzero : ∀ c, t≤c → e c=0)
    (mu : YoungDiagram) (u : Tableau (staircase (k-2)).card mu)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (hpi : (containedPath h hh d (witnessPathSize k) m).colLen 0≤4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0≤4) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap (independentTensor (spechtRep u) (spechtRep s))
      (witnessCoreComplementBlockCyclic k b delta hp.staircase_bound z).toRepresentation,
      Function.Injective F := by
  obtain ⟨E,hEcore⟩ := witness_core_universal_embedding k b delta hp.staircase_bound mu u
  obtain ⟨J,hJ⟩ := containedWitness_complement_embedding hh he k b delta hp htm hroom
    hclear hcapacity hsize hzero s hpi hc hE z
  let A := independentTensorMap E J
  let B := witnessCoreComplementFactorMap k b delta hp.staircase_bound z
  exact ⟨B.comp A,
    (witnessCoreComplementFactorMap_bijective k b delta hp.staircase_bound z).1.comp
      (independentTensorMap_injective E J hEcore hJ)⟩

/-- Core universality and support of the full original complement compose into
an injective independent full-group map into the full product carrier.
No sector induction or target Specht identification is asserted. -/
theorem containedWitness_core_complement_embedding
    {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta) (hzero : ∀ c, t≤c → e c=0)
    (mu : YoungDiagram) (u : Tableau (staircase (k-2)).card mu)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (hpi : (containedPath h hh d (witnessPathSize k) m).colLen 0≤4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0≤4) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap (independentTensor (spechtRep u) (spechtRep s))
      ((witnessCoreComplementCyclic k b delta hp.staircase_bound z).toRepresentation.comp
        (sumPermHom (witnessBinaryCut k b delta hp.staircase_bound z))),
      Function.Injective F := by
  obtain ⟨F,hF⟩ := containedWitness_core_complement_block_embedding hh he k b delta hp
    htm hroom hclear hcapacity hsize hzero mu u s hpi hc hE z
  exact ⟨(witnessCoreComplementBlockInclusion k b delta hp.staircase_bound z).comp F,
    (witnessCoreComplementBlockInclusion_injective k b delta hp.staircase_bound z).comp hF⟩
end
end HSTZ
#print axioms HSTZ.witnessCoreComplement_block_le
#print axioms HSTZ.witnessCoreComplementBlockInclusion_injective
#print axioms HSTZ.witnessCoreComplementFactorMap_bijective
#print axioms HSTZ.witnessCoreComplementFactorMap_tmul
#print axioms HSTZ.containedWitness_core_complement_embedding

#print axioms HSTZ.containedWitness_core_complement_block_embedding
