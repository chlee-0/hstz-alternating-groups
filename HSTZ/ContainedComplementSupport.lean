import HSTZ.ContainedComplementCoefficient

/-! Forward support of the full complement cyclic carrier. Reuses the forward
pairing and irreducibility interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This file does not construct a common nondegenerate basis, assemble the core, or
prove the full HSTZ statement. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem containedWitness_complement_embedding
    {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta) (hzero : ∀ c, t≤c → e c=0)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (hpi : (containedPath h hh d (witnessPathSize k) m).colLen 0≤4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0≤4) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep (witnessComplementSize k b delta)
        ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
          (witnessDiagram k b delta hp.staircase_bound).colLen 0))
        (witnessComplementPairWord k b delta hp.staircase_bound z)).toRepresentation,
      Function.Injective F := by
  obtain ⟨sigma,L,hL,hnz⟩ := containedMovedWitness_contraction_nonzero hh he k b delta hp
    htm hroom hclear hcapacity hsize hzero s hpi hc hE z
  let P := containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma
  let x : (spechtSub s).toSubmodule :=
    ⟨wordRep _ _ P.symm (polytabloid s),
      (spechtSub s).apply_mem_toSubmodule P.symm (mem_cyclic _ _)⟩
  obtain ⟨F,hF⟩ := hom_to_cyclic_of_pair L (spechtSub s) x
    (witnessComplementPairWord k b delta hp.staircase_bound z)
    (witnessComplementPairWord_real k b delta hp.staircase_bound z) hnz
  change Representation.IntertwiningMap (spechtRep s)
    (cyclic (wordRep (witnessComplementSize k b delta)
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
      (witnessComplementPairWord k b delta hp.staircase_bound z)).toRepresentation at F
  letI := specht_irreducible s
  exact ⟨F,(Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩
end
end HSTZ
#print axioms HSTZ.containedWitness_complement_embedding
