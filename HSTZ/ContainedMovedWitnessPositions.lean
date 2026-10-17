import HSTZ.ContainedAttachmentPlacement

/-! Moved placement of the full witness positions, keeping the cleared path slots in
place. The attachment permutation `sigma` is an arbitrary parameter. Uses
declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (sigma : Equiv.Perm (Fin (containedAttachment e he m).card))
local notation "Q" => containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma

def containedMovedWitnessPositions : Equiv.Perm (Fin (witnessComplementSize k b delta)) :=
  (witnessComplementOrder k b delta).symm.trans
    ((Equiv.sumCongr (Equiv.refl _) (finCongr (containedAttachment_witness_card he b delta m hsize))).trans (Q))
local notation "P" => containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma

theorem containedMovedWitnessPositions_path (i : Fin (witnessPathSize k)) :
    (P) (witnessComplementOrder k b delta (.inl i))=
      containedFactorPositions hh he htm hroom hclear hcapacity s (.inl i) := by
  simp only [containedMovedWitnessPositions,Equiv.trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl,Equiv.refl_apply,containedAttachmentPlacedPositions_path]

theorem containedMovedWitnessPositions_attachment (i : Fin (witnessAttachment b delta).card) :
    (P) (witnessComplementOrder k b delta (.inr i))=
      (Q) (.inr (finCongr (containedAttachment_witness_card he b delta m hsize) i)) := by
  simp only [containedMovedWitnessPositions,Equiv.trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inr]

theorem containedMovedWitnessPositions_flag (hzero : ∀ c, t ≤ c → e c=0)
    (i : Fin (witnessComplementSize k b delta)) :
    (rowWord s ((P) i)).val < d ↔ witnessComplementPathMask k b delta i := by
  obtain ⟨j,rfl⟩ := (witnessComplementOrder k b delta).surjective i
  cases j with
  | inl j =>
    rw [containedMovedWitnessPositions_path]
    have hr := containedFactorPositions_path_flag hh he htm hroom hclear hcapacity s j
    simpa [witnessComplementPathMask] using hr
  | inr j =>
    rw [containedMovedWitnessPositions_attachment]
    have hr := containedAttachmentPlacedPositions_flag hh he htm hroom hclear hcapacity s sigma hzero
      (.inr (finCongr (containedAttachment_witness_card he b delta m hsize) j))
    simpa only [witnessComplementPathMask, Equiv.symm_apply_apply,Sum.isLeft_inr,
      Bool.false_eq_true,iff_false] using hr

def containedMovedWitnessColumnGroup :=
  fiberGroup (fun i => (s (containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma i)).val.2)

def containedMovedWitnessColumnEquiv :
    containedMovedWitnessColumnGroup hh he k b delta htm hroom hclear hcapacity hsize s sigma ≃ columnGroup s :=
  fiberRelabel (containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma)
    (fun i => (s i).val.2)

theorem containedMovedWitnessColumnEquiv_value
    (g : containedMovedWitnessColumnGroup hh he k b delta htm hroom hclear hcapacity hsize s sigma)
    (i : Fin (witnessComplementSize k b delta)) :
    (containedMovedWitnessColumnEquiv hh he k b delta htm hroom hclear hcapacity hsize s sigma g).val i =
      containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma
        (g.val ((containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma).symm i)) := rfl

theorem containedMovedWitnessColumnEquiv_inverse
    (g : columnGroup s) (i : Fin (witnessComplementSize k b delta)) :
    ((containedMovedWitnessColumnEquiv hh he k b delta htm hroom hclear hcapacity hsize s sigma).symm g).val.symm i =
      (containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma).symm
        (g.val.symm (containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma i)) := rfl

theorem containedMovedWitnessPolytabloid_reindex :
    wordRep _ _ (containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma).symm
      (polytabloid s) =
      altWord (containedMovedWitnessColumnGroup hh he k b delta htm hroom hclear hcapacity hsize s sigma)
        (rowWord s ∘ containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma) := by
  funext w
  rw [polytabloid_eq_altWord]
  change altWord (fiberGroup (fun i => (s i).val.2)) (rowWord s)
    (w ∘ (containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma).symm) = _
  exact altWord_fiber_relabel _ _ _ w
end
end
end HSTZ
#print axioms HSTZ.containedMovedWitnessPositions
#print axioms HSTZ.containedMovedWitnessPositions_path
#print axioms HSTZ.containedMovedWitnessPositions_attachment
#print axioms HSTZ.containedMovedWitnessPositions_flag
#print axioms HSTZ.containedMovedWitnessColumnGroup
#print axioms HSTZ.containedMovedWitnessColumnEquiv
#print axioms HSTZ.containedMovedWitnessColumnEquiv_value
#print axioms HSTZ.containedMovedWitnessColumnEquiv_inverse
#print axioms HSTZ.containedMovedWitnessPolytabloid_reindex
