import HSTZ.WitnessBinaryCut

/-! Ordered full complement cells under every original caller tableau.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The ordered cells preserve the path and canonical attachment enumeration. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def witnessComplementCell (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessComplementSize k b delta)) : (witnessDiagram k b delta hk).cells :=
  witnessCutOrderedCells k b delta hk (.inr ((witnessComplementOrder k b delta).symm i))

theorem witnessComplementCell_path (k b delta : ℕ) (hk : 5 ≤ k)
    (j : Fin (witnessPathSize k)) :
    witnessComplementCell k b delta hk (witnessComplementOrder k b delta (.inl j))=
      witnessPathPositionCell k b delta hk j := by
  simp only [witnessComplementCell,Equiv.symm_apply_apply]
  rfl

theorem witnessComplementCell_attachment (k b delta : ℕ) (hk : 5 ≤ k)
    (j : Fin (witnessAttachment b delta).card) :
    witnessComplementCell k b delta hk (witnessComplementOrder k b delta (.inr j))=
      witnessAttachmentCell k b delta hk (canonicalTableau (witnessAttachment b delta) rfl j) := by
  simp only [witnessComplementCell,Equiv.symm_apply_apply]
  rfl

theorem witnessComplementCell_original (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin (witnessComplementSize k b delta)) :
    t ((witnessBinaryCut k b delta hk t).symm (.inr i))=witnessComplementCell k b delta hk i := by
  change t (t.symm (witnessCutOrderedCells k b delta hk
    (.inr ((witnessComplementOrder k b delta).symm i))))=_
  exact t.apply_symm_apply _

end
end HSTZ
#print axioms HSTZ.witnessComplementCell_path
#print axioms HSTZ.witnessComplementCell_attachment
#print axioms HSTZ.witnessComplementCell_original
