import HSTZ.IntertwiningCompat
import HSTZ.ContainedMovedWitnessNonmixed

/-! The moved full column contraction restricts to the survivor group.
Reuses `altWord_sector` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The separated covectors are explicit; common flags and a nonzero contraction are not
proved in this file. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta) (hzero : ∀ c, t ≤ c → e c=0)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
variable (sigma : Equiv.Perm (Fin (containedAttachment e he m).card))
local notation "P" => containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma
include hzero

theorem containedMovedWitness_assignment_flag (g : columnGroup s) :
    (∀ j, (rowWord s (g.val.symm j)).val < d ↔ (rowWord s j).val < d) ↔
    witnessFlagMatches k b delta (fun j => j.val < d) (rowWord s ∘ g.val.symm ∘ P) := by
  constructor
  · intro hg i
    exact (hg ((P) i)).trans
      (containedMovedWitnessPositions_flag hh he k b delta htm hroom hclear hcapacity hsize s sigma hzero i)
  · intro hg j
    have hi := hg ((P).symm j)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hi.trans
      (containedMovedWitnessPositions_flag hh he k b delta htm hroom hclear hcapacity hsize s sigma hzero ((P).symm j)).symm

/-- The match predicate is exactly membership in the full column survivor group. -/
theorem containedMovedWitness_assignment_survivor (g : columnGroup s) :
    witnessFlagMatches k b delta (fun j => j.val < d) (rowWord s ∘ g.val.symm ∘ P) ↔
      g.val ∈ containedTargetSurvivorGroup hh he s (d:=d) := by
  rw [← containedMovedWitness_assignment_flag hh he k b delta htm hroom hclear hcapacity hsize hzero s sigma g]
  change g.val.symm ∈ sectorGroup (fun i => (rowWord s i).val < d) ↔
    g.val ∈ columnGroup s ⊓ sectorGroup (fun i => (rowWord s i).val < d)
  simp only [Subgroup.mem_inf,g.property,true_and]
  exact inv_mem_iff

/-- Target-to-source conjugation of the full column group preserves sign. -/
theorem containedMovedWitnessColumnEquiv_sign (g : columnGroup s) :
    signC (((containedMovedWitnessColumnEquiv hh he k b delta htm hroom hclear hcapacity hsize s sigma).symm g).val)=
      signC g.val := by
  change signC ((P).symm.permCongr g.val)=signC g.val
  simp only [signC_def,Equiv.Perm.sign_permCongr]

variable {n : ℕ} (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
    (L : Fin ((containedWhole h e hh he d (witnessPathSize k) m).colLen 0) → Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)
    (hL : witnessFlagSeparated k b delta hp (fun j => j.val < d) L)
include hL

/-- The sum over the full column group equals the survivor sum, given the cleared
prefix and separated covectors. -/
theorem containedMovedWitness_full_survivor_contraction :
    dotProduct (wordMap L (wordRep _ _ (P).symm (polytabloid s)))
      (witnessComplementPairWord k b delta hp.staircase_bound z)=
    dotProduct (wordMap L (wordRep _ _ (P).symm
      (altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s))))
      (witnessComplementPairWord k b delta hp.staircase_bound z) := by
  classical
  letI := Fintype.ofFinite (columnGroup s)
  have hs : coordinateProjection (fun a => ∀ i, (a i).val < d ↔ (rowWord s i).val < d)
      (polytabloid s)=altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s) := by
    rw [polytabloid_eq_altWord]
    exact altWord_sector _ _ (fun j => j.val < d) _ (fun _ => Iff.rfl)
  rw [← hs,polytabloid_eq_altWord]
  unfold altWord
  change dotProduct ((wordMap L).toLinearMap ((wordRep _ _ (P).symm) _)) _ =
    dotProduct ((wordMap L).toLinearMap ((wordRep _ _ (P).symm) (coordinateProjection _ _))) _
  simp only [map_sum,map_smul,sum_dotProduct,smul_dotProduct]
  apply Finset.sum_congr rfl
  intro g hg
  rw [wordRep_single,coordinateProjection_single]
  simp only [Function.comp_apply,Equiv.Perm.inv_def]
  by_cases hm : ∀ j, (rowWord s (g.val.symm j)).val < d ↔ (rowWord s j).val < d
  · rw [if_pos hm,wordRep_single]
  · rw [if_neg hm]
    simp only [map_zero,zero_dotProduct,smul_zero]
    rw [wordRep_single]
    simp only [Equiv.Perm.inv_def,Equiv.symm_symm]
    change signC g.val • dotProduct (wordMap L (Pi.single (rowWord s ∘ g.val.symm ∘ P) 1))
      (witnessComplementPairWord k b delta hp.staircase_bound z)=0
    have ha : ¬witnessFlagMatches k b delta (fun j => j.val < d) (rowWord s ∘ g.val.symm ∘ P) := by
      intro ha
      exact hm ((containedMovedWitness_assignment_flag hh he k b delta htm hroom hclear hcapacity hsize hzero s sigma g).mpr ha)
    rw [containedMovedWitness_unmatched_term_zero hh he k b delta hp htm hroom hclear hcapacity hsize hzero s sigma z L hL g ha,smul_zero]

/-- All survivor terms match, relating the full-source contraction to the projection. -/
theorem containedMovedWitness_survivor_projection :
    dotProduct (wordMap L (wordRep _ _ (P).symm
      (altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s))))
      (witnessComplementPairWord k b delta hp.staircase_bound z)=
    dotProduct (wordMap L (wordRep _ _ (P).symm
      (altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s))))
      (witnessComplementLowProjection k b delta hp
        (witnessComplementPairWord k b delta hp.staircase_bound z)) := by
  classical
  letI := Fintype.ofFinite (containedTargetSurvivorGroup hh he s (d:=d))
  unfold altWord
  change dotProduct ((wordMap L).toLinearMap ((wordRep _ _ (P).symm) _)) _ =
    dotProduct ((wordMap L).toLinearMap ((wordRep _ _ (P).symm) _)) _
  simp only [map_sum,map_smul,sum_dotProduct,smul_dotProduct,wordRep_single,
    Equiv.Perm.inv_def,Equiv.symm_symm]
  apply Finset.sum_congr rfl
  intro g hg
  let g' : columnGroup s := ⟨g.val,g.property.1⟩
  have ha := (containedMovedWitness_assignment_survivor hh he k b delta htm hroom hclear hcapacity hsize hzero s sigma g').mpr g.property
  exact congrArg (fun v : ℂ => signC g.val • v)
    (witnessComplement_matched_projection k b delta hp z _ L hL _ ha)

/-- The survivor target is paired with the placed selected source. The minus sign
from the exchange and projection is explicit; it is not replaced by the paper's
shuffle sign. -/
theorem containedMovedWitness_selected_survivor_contraction :
    dotProduct (wordMap L (wordRep _ _ (P).symm (polytabloid s)))
      (witnessComplementPairWord k b delta hp.staircase_bound z)=
    -dotProduct (wordMap L
      (altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s)))
      (wordRep _ _ (P) (witnessSelectedComplementPairWord k b delta hp)) := by
  rw [containedMovedWitness_full_survivor_contraction hh he k b delta hp htm hroom hclear hcapacity hsize hzero s sigma z L hL,
    containedMovedWitness_survivor_projection hh he k b delta hp htm hroom hclear hcapacity hsize hzero s sigma z L hL,
    witness_selected_pair_projection,dotProduct_neg]
  have hi : wordMap L (wordRep _ _ (P).symm
      (altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s)))=
    wordRep _ _ (P).symm (wordMap L
      (altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s))) :=
    (wordMap L).map_action (P).symm _
  rw [hi,wordPair_move]
  rfl
end
end
end HSTZ
#print axioms HSTZ.containedMovedWitness_assignment_flag
#print axioms HSTZ.containedMovedWitness_assignment_survivor
#print axioms HSTZ.containedMovedWitness_full_survivor_contraction

#print axioms HSTZ.containedMovedWitness_survivor_projection
#print axioms HSTZ.containedMovedWitness_selected_survivor_contraction

#print axioms HSTZ.containedMovedWitnessColumnEquiv_sign
