import HSTZ.WitnessEndpointExchange

/-! All coordinates of the exchanged complement bases.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The exceptional path endpoint is moved explicitly rather than normalized away. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem witnessComplementRowBase_path (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) :
    witnessComplementRowBase k b delta hk (witnessComplementOrder k b delta (.inl i))=
      witnessPathRowBase k b delta hk i := by
  apply Fin.ext
  change (witnessRowRotation k b delta hk (witnessComplementCell k b delta hk
    (witnessComplementOrder k b delta (.inl i)))).val.2=_
  rw [witnessComplementCell_path]
  rfl

theorem witnessComplementColumnBase_path (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) :
    witnessComplementColumnBase k b delta hk (witnessComplementOrder k b delta (.inl i))=
      witnessPathColumnBase k b delta hk i := by
  apply Fin.ext
  change (witnessColumnRotation k b delta hk (witnessComplementCell k b delta hk
    (witnessComplementOrder k b delta (.inl i)))).val.1=_
  rw [witnessComplementCell_path]
  rfl

theorem witnessComplementRowBase_origin (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta) :
    (witnessComplementRowBase k b delta hk (witnessComplementOrigin k b delta hr)).val=1 := by
  change (witnessRowRotation k b delta hk (witnessComplementCell k b delta hk
    (witnessComplementOrder k b delta (.inr (witnessAttachmentOriginPosition b delta hr))))).val.2=1
  rw [witnessComplementCell_attachment,witnessAttachmentOriginPosition_cell]
  change witnessRowForward k b 0 (k-1+0)=1
  unfold witnessRowForward witnessFirstRowForward
  split_ifs <;> omega

theorem witnessComplementColumnBase_origin (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta) :
    (witnessComplementColumnBase k b delta hk (witnessComplementOrigin k b delta hr)).val=0 := by
  change (witnessColumnRotation k b delta hk (witnessComplementCell k b delta hk
    (witnessComplementOrder k b delta (.inr (witnessAttachmentOriginPosition b delta hr))))).val.1=0
  rw [witnessComplementCell_attachment,witnessAttachmentOriginPosition_cell]
  change (if 0<k-2-(k-1+0) then 0+2 else 0-(k-2-(k-1+0)))=0
  have he : k-2-(k-1+0)=0 := by omega
  simp only [he,Nat.not_lt_zero,if_false,Nat.sub_zero]

theorem witnessComplementRowBase_endpoint (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessComplementRowBase k b delta hk (witnessComplementEndpoint k b delta)).val=
      witnessFirstRowForward k b (k+b+delta-1) := by
  rw [witnessComplementEndpoint,witnessComplementRowBase_path]
  exact witnessPathRowBase_endpoint k b delta hk

theorem witnessComplementColumnBase_endpoint (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessComplementColumnBase k b delta hk (witnessComplementEndpoint k b delta)).val=0 := by
  rw [witnessComplementEndpoint,witnessComplementColumnBase_path]
  exact witnessPathColumnBase_endpoint k b delta hk

def witnessExchangedRowBase (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta) :
    Fin (witnessComplementSize k b delta) →
      Fin ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  witnessComplementRowBase k b delta hk ∘ witnessEndpointExchangePerm k b delta hr

theorem witnessExchangedRowBase_all (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta)
    (i : Fin (witnessComplementSize k b delta)) :
    (witnessExchangedRowBase k b delta hk hr i).val=
      if i=witnessComplementEndpoint k b delta then 1
      else if i=witnessComplementOrigin k b delta hr then
        (witnessComplementRowBase k b delta hk (witnessComplementEndpoint k b delta)).val
      else (witnessComplementRowBase k b delta hk i).val := by
  classical
  simp only [witnessExchangedRowBase,Function.comp_apply,witnessEndpointExchangePerm,
    Equiv.swap_apply_def]
  split_ifs <;> first | exact witnessComplementRowBase_origin k b delta hk hr | rfl

theorem witnessEndpointExchange_column_fixed (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta) :
    witnessComplementColumnBase k b delta hk ∘ witnessEndpointExchangePerm k b delta hr=
      witnessComplementColumnBase k b delta hk := by
  classical
  funext i
  apply Fin.ext
  simp only [Function.comp_apply,witnessEndpointExchangePerm,Equiv.swap_apply_def]
  split_ifs <;> subst_vars
  · rw [witnessComplementColumnBase_origin,witnessComplementColumnBase_endpoint]
  · rw [witnessComplementColumnBase_endpoint,witnessComplementColumnBase_origin]
  · rfl

end
end HSTZ
#print axioms HSTZ.witnessComplementRowBase_path
#print axioms HSTZ.witnessComplementColumnBase_path
#print axioms HSTZ.witnessComplementRowBase_origin
#print axioms HSTZ.witnessComplementColumnBase_origin
#print axioms HSTZ.witnessComplementRowBase_endpoint
#print axioms HSTZ.witnessComplementColumnBase_endpoint
#print axioms HSTZ.witnessExchangedRowBase_all
#print axioms HSTZ.witnessEndpointExchange_column_fixed
