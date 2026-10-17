import HSTZ.IntertwiningCompat
import HSTZ.WitnessAttachmentHSelectedSupport
import HSTZ.WitnessAttachmentHParitySupport
import HSTZ.SpechtSignTransport
import HSTZ.ParityCapacity

/-! Column-parity targets in the selected attachment cyclic space. Uses interfaces
from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The H contraction, its inverse and both sign factors are kept explicit. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def AttachmentEvenColumns (mu : YoungDiagram) : Prop := ∀ c, mu.colLen c % 2 = 0

def AttachmentOneOddColumn (mu : YoungDiagram) (a : ℕ) : Prop :=
  mu.colLen a % 2 = 1 ∧ ∀ c, c ≠ a → mu.colLen c % 2 = 0

theorem attachmentEvenColumns_transpose (mu : YoungDiagram)
    (he : AttachmentEvenColumns mu) : AttachmentEvenRows mu.transpose := by
  intro r
  simpa only [YoungDiagram.rowLen_transpose] using he r

theorem attachmentOneOddColumn_transpose (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddColumn mu a) : AttachmentOneOddRow mu.transpose a := by
  constructor
  · simpa only [YoungDiagram.rowLen_transpose] using ho.1
  · intro r hr
    simpa only [YoungDiagram.rowLen_transpose] using ho.2 r hr

/- Private composition spelling only; the Specht sign map is reused. -/
private def attachmentSignBack {n : ℕ} {mu : YoungDiagram} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (t : Tableau n mu)
    (sigma : Representation ℂ (Equiv.Perm (Fin n)) V)
    (G : Representation.IntertwiningMap (spechtRep (transposeTableau t)) (signTwist sigma)) :
    Representation.IntertwiningMap (spechtRep t) sigma where
  toLinearMap := G.toLinearMap.comp (spechtSignMap t).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change G.toLinearMap ((spechtSignMap t).toLinearMap (spechtRep t g x)) =
      sigma g (G.toLinearMap ((spechtSignMap t).toLinearMap x))
    have hs := (spechtSignMap t).map_action g x
    change (spechtSignMap t).toLinearMap (spechtRep t g x) =
      signC g • spechtRep (transposeTableau t) g (spechtSignMap t x) at hs
    rw [hs]
    change G.toLinearMap (signC g • spechtRep (transposeTableau t) g (spechtSignMap t x)) = _
    rw [map_smul]
    have hG := G.map_action g (spechtSignMap t x)
    change G.toLinearMap (spechtRep (transposeTableau t) g (spechtSignMap t x)) =
      signC g • sigma g (G (spechtSignMap t x)) at hG
    rw [hG]
    change signC g • (signC g • sigma g (G (spechtSignMap t x))) = _
    rw [smul_smul,signC_mul_self,one_smul]
    rfl

private theorem attachmentSignBack_injective {n : ℕ} {mu : YoungDiagram} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (t : Tableau n mu)
    (sigma : Representation ℂ (Equiv.Perm (Fin n)) V)
    (G : Representation.IntertwiningMap (spechtRep (transposeTableau t)) (signTwist sigma))
    (hG : Function.Injective G.toLinearMap) :
    Function.Injective (attachmentSignBack t sigma G).toLinearMap :=
  hG.comp (spechtSignMap_bijective t).1

theorem witnessSelectedAttachment_even_embedding (k b : ℕ)
    (hp : PaperWitnessGuard k b 0) {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenColumns mu)
    (ht : mu.rowLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (witnessAttachmentCyclic k b 0 hp).toRepresentation, Function.Injective F.toLinearMap := by
  obtain ⟨P,hP⟩ := attachmentHTensor_even_embedding (transposeTableau t)
    (attachmentEvenColumns_transpose mu he) (by simpa only [YoungDiagram.colLen_transpose] using ht)
  obtain ⟨J,hJ⟩ := witnessSelectedAttachmentH_embedding k b 0 hp
  exact ⟨attachmentSignBack t (witnessAttachmentCyclic k b 0 hp).toRepresentation (J.comp P),
    attachmentSignBack_injective t _ (J.comp P) (hJ.comp hP)⟩

theorem witnessSelectedAttachment_odd_embedding (k b : ℕ)
    (hp : PaperWitnessGuard k b 1) {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ) (ho : AttachmentOneOddColumn mu a)
    (ht : mu.rowLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (witnessAttachmentCyclic k b 1 hp).toRepresentation, Function.Injective F.toLinearMap := by
  obtain ⟨P,hP⟩ := attachmentHTensor_odd_embedding (transposeTableau t) a
    (attachmentOneOddColumn_transpose mu a ho) (by simpa only [YoungDiagram.colLen_transpose] using ht)
  obtain ⟨J,hJ⟩ := witnessSelectedAttachmentH_embedding k b 1 hp
  exact ⟨attachmentSignBack t (witnessAttachmentCyclic k b 1 hp).toRepresentation (J.comp P),
    attachmentSignBack_injective t _ (J.comp P) (hJ.comp hP)⟩

/-- Capacity-selection parity predicate, with the paper's guard unchanged. -/
theorem witnessSelectedAttachment_parity_embedding (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b delta).card mu)
    (hc : ColumnParity mu.colLen delta) (ht : mu.rowLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (witnessAttachmentCyclic k b delta hp).toRepresentation, Function.Injective F.toLinearMap := by
  by_cases hd : delta = 0
  · subst delta
    have he : AttachmentEvenColumns mu := by simpa [ColumnParity,AttachmentEvenColumns] using hc
    exact witnessSelectedAttachment_even_embedding k b hp t he ht
  · have hd1 : delta = 1 := by have hb := hp.parity; omega
    subst delta
    have ho : ∃ a, AttachmentOneOddColumn mu a := by
      simpa [ColumnParity,AttachmentOneOddColumn] using hc
    obtain ⟨a,ha⟩ := ho
    exact witnessSelectedAttachment_odd_embedding k b hp t a ha ht

end
end HSTZ
#print axioms HSTZ.attachmentEvenColumns_transpose
#print axioms HSTZ.attachmentOneOddColumn_transpose
#print axioms HSTZ.witnessSelectedAttachment_even_embedding
#print axioms HSTZ.witnessSelectedAttachment_odd_embedding
#print axioms HSTZ.witnessSelectedAttachment_parity_embedding
