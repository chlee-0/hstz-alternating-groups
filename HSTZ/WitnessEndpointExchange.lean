import HSTZ.WitnessComplementFibers
import HSTZ.WitnessTableau

/-! The transposition exchanging the path endpoint and the attachment origin, as an
element of the complement row group. It has sign `-1` and does not preserve the path
sector. Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem paperWitness_attachment_positive (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) : 0<b+delta := by
  have hr := hp.positive_remainder
  omega

def witnessAttachmentOrigin (b delta : ℕ) (hr : 0<b+delta) :
    (witnessAttachment b delta).cells :=
  ⟨(0,0),(mem_witnessAttachment b delta 0 0).mpr (.inl ⟨rfl,hr⟩)⟩

def witnessAttachmentOriginPosition (b delta : ℕ) (hr : 0<b+delta) :
    Fin (witnessAttachment b delta).card :=
  (witnessCanonicalAttachment b delta).symm (witnessAttachmentOrigin b delta hr)

theorem witnessAttachmentOriginPosition_cell (b delta : ℕ) (hr : 0<b+delta) :
    witnessCanonicalAttachment b delta (witnessAttachmentOriginPosition b delta hr)=
      witnessAttachmentOrigin b delta hr :=
  (witnessCanonicalAttachment b delta).apply_symm_apply _

def witnessComplementEndpoint (k b delta : ℕ) : Fin (witnessComplementSize k b delta) :=
  witnessComplementOrder k b delta (.inl (witnessPathEndpoint k))
def witnessComplementOrigin (k b delta : ℕ) (hr : 0<b+delta) :
    Fin (witnessComplementSize k b delta) :=
  witnessComplementOrder k b delta (.inr (witnessAttachmentOriginPosition b delta hr))

theorem witnessComplementEndpoint_ne_origin (k b delta : ℕ) (hr : 0<b+delta) :
    witnessComplementEndpoint k b delta≠witnessComplementOrigin k b delta hr := by
  intro he
  have hh := (witnessComplementOrder k b delta).injective he
  cases hh

def witnessEndpointExchangePerm (k b delta : ℕ) (hr : 0<b+delta) :
    Equiv.Perm (Fin (witnessComplementSize k b delta)) :=
  Equiv.swap (witnessComplementEndpoint k b delta) (witnessComplementOrigin k b delta hr)

theorem witnessEndpointExchange_mem (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta) :
    witnessEndpointExchangePerm k b delta hr∈witnessComplementRowGroup k b delta hk := by
  apply witness_complement_row_cross_swap k b delta hk
  rw [witnessPathPositionCell_endpoint,witnessAttachmentOriginPosition_cell]
  rfl

def witnessEndpointExchange (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta) :
    witnessComplementRowGroup k b delta hk :=
  ⟨witnessEndpointExchangePerm k b delta hr,witnessEndpointExchange_mem k b delta hk hr⟩

theorem witnessEndpointExchange_sign (k b delta : ℕ) (hr : 0<b+delta) :
    signC (witnessEndpointExchangePerm k b delta hr)= -1 := by
  simp [witnessEndpointExchangePerm,signC_def,
    Equiv.Perm.sign_swap (witnessComplementEndpoint_ne_origin k b delta hr)]

theorem witnessEndpointExchange_not_sector (k b delta : ℕ) (hr : 0<b+delta) :
    witnessEndpointExchangePerm k b delta hr∉sectorGroup (witnessComplementPathMask k b delta) :=
  witness_complement_cross_swap_not_sector k b delta (witnessPathEndpoint k)
    (witnessAttachmentOriginPosition b delta hr)

end
end HSTZ
#print axioms HSTZ.paperWitness_attachment_positive
#print axioms HSTZ.witnessAttachmentOriginPosition_cell
#print axioms HSTZ.witnessComplementEndpoint_ne_origin
#print axioms HSTZ.witnessEndpointExchange_mem
#print axioms HSTZ.witnessEndpointExchange_sign
#print axioms HSTZ.witnessEndpointExchange_not_sector
