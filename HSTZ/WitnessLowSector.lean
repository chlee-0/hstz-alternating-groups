import HSTZ.WitnessLowMask

/-! The selected low-row sector after the endpoint/origin exchange.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The full row group is intersected with the ordered path stabilizer. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def witnessSelectedRowWord (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    WordSpace (witnessComplementSize k b delta)
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0) :=
  altWord (witnessComplementRowGroup k b delta hp.staircase_bound ⊓
    sectorGroup (witnessComplementPathMask k b delta))
    (witnessExchangedRowBase k b delta hp.staircase_bound
      (paperWitness_attachment_positive k b delta hp))

theorem witness_selected_row_sector (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    coordinateProjection (fun a => ∀ i, (a i).val<2 ↔ witnessComplementPathMask k b delta i)
      (witnessComplementRowWord k b delta hp.staircase_bound t)=
        -witnessSelectedRowWord k b delta hp := by
  rw [witness_complement_row_alternant]
  have he := altWord_sector_rotated
    (witnessComplementRowGroup k b delta hp.staircase_bound)
    (witnessComplementRowBase k b delta hp.staircase_bound)
    (fun a => a.val<2) (witnessComplementPathMask k b delta)
    (witnessEndpointExchange k b delta hp.staircase_bound
      (paperWitness_attachment_positive k b delta hp))
    (witnessExchangedRowBase_low_mask k b delta hp)
  change _ = signC (witnessEndpointExchangePerm k b delta
    (paperWitness_attachment_positive k b delta hp)) • witnessSelectedRowWord k b delta hp at he
  rw [witnessEndpointExchange_sign,neg_one_smul] at he
  exact he

end
end HSTZ
#print axioms HSTZ.witness_selected_row_sector
