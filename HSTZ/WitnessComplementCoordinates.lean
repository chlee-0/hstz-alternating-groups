import HSTZ.WitnessComplementCells
import HSTZ.WitnessCoreFactorization
import HSTZ.WitnessAttachmentWords

/-! Rotated full complement words and signed full-fiber covariance. Uses interfaces
from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The width and height alphabets stay separate, and the exceptional endpoint is kept.
These alternants do not assert independent path/attachment support. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def witnessComplementRowGroup (k b delta : ℕ) (hk : 5 ≤ k) :
    Subgroup (Equiv.Perm (Fin (witnessComplementSize k b delta))) :=
  fiberGroup (fun i : Fin (witnessComplementSize k b delta) => (witnessComplementCell k b delta hk i).val.1)
def witnessComplementColumnGroup (k b delta : ℕ) (hk : 5 ≤ k) :
    Subgroup (Equiv.Perm (Fin (witnessComplementSize k b delta))) :=
  fiberGroup (fun i : Fin (witnessComplementSize k b delta) => (witnessComplementCell k b delta hk i).val.2)

theorem witness_complement_row_fiber (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    fiberGroup (fun i : Fin (witnessComplementSize k b delta) => (t ((witnessBinaryCut k b delta hk t).symm (.inr i))).val.1)=
      witnessComplementRowGroup k b delta hk := by
  ext g
  change (∀ i, (t ((witnessBinaryCut k b delta hk t).symm (.inr (g i)))).val.1=
    (t ((witnessBinaryCut k b delta hk t).symm (.inr i))).val.1) ↔
    (∀ i, (witnessComplementCell k b delta hk (g i)).val.1=
      (witnessComplementCell k b delta hk i).val.1)
  simp only [witnessComplementCell_original]

theorem witness_complement_column_fiber (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    fiberGroup (fun i : Fin (witnessComplementSize k b delta) => (t ((witnessBinaryCut k b delta hk t).symm (.inr i))).val.2)=
      witnessComplementColumnGroup k b delta hk := by
  ext g
  change (∀ i, (t ((witnessBinaryCut k b delta hk t).symm (.inr (g i)))).val.2=
    (t ((witnessBinaryCut k b delta hk t).symm (.inr i))).val.2) ↔
    (∀ i, (witnessComplementCell k b delta hk (g i)).val.2=
      (witnessComplementCell k b delta hk i).val.2)
  simp only [witnessComplementCell_original]


def witnessComplementRowBase (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessComplementSize k b delta)) :
    Fin ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  let x := witnessRowRotation k b delta hk (witnessComplementCell k b delta hk i)
  ⟨x.val.2,by
    rw [YoungDiagram.colLen_transpose]
    exact YoungDiagram.mem_iff_lt_rowLen.mp
      ((witnessDiagram k b delta hk).up_left_mem (Nat.zero_le _) le_rfl x.property)⟩

def witnessComplementColumnBase (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessComplementSize k b delta)) :
    Fin ((witnessDiagram k b delta hk).colLen 0) :=
  let x := witnessColumnRotation k b delta hk (witnessComplementCell k b delta hk i)
  ⟨x.val.1,YoungDiagram.mem_iff_lt_colLen.mp
    ((witnessDiagram k b delta hk).up_left_mem le_rfl (Nat.zero_le _) x.property)⟩

theorem witness_complement_row_base (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    rightWord (witnessBinaryCut k b delta hk t)
      (rowWord (transposeTableau t) ∘ (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)))=
      witnessComplementRowBase k b delta hk := by
  funext i
  apply Fin.ext
  change (t ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))
    ((witnessBinaryCut k b delta hk t).symm (.inr i)))).val.2=_
  rw [witnessRowRotationPositions_cell,witnessComplementCell_original]
  rfl

theorem witness_complement_column_base (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    rightWord (witnessBinaryCut k b delta hk t)
      (rowWord t ∘ (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n)))=
      witnessComplementColumnBase k b delta hk := by
  funext i
  apply Fin.ext
  change (t ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))
    ((witnessBinaryCut k b delta hk t).symm (.inr i)))).val.1=_
  rw [witnessColumnRotationPositions_cell,witnessComplementCell_original]
  rfl

theorem witness_complement_row_alternant (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessComplementRowWord k b delta hk t=
      altWord (witnessComplementRowGroup k b delta hk) (witnessComplementRowBase k b delta hk) := by
  unfold witnessComplementRowWord
  rw [witness_complement_row_fiber,witness_complement_row_base]

theorem witness_complement_column_alternant (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessComplementColumnWord k b delta hk t=
      altWord (witnessComplementColumnGroup k b delta hk) (witnessComplementColumnBase k b delta hk) := by
  unfold witnessComplementColumnWord
  rw [witness_complement_column_fiber,witness_complement_column_base]

theorem witness_complement_row_covariance (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (g : witnessComplementRowGroup k b delta hk) :
    altWord (witnessComplementRowGroup k b delta hk)
      (witnessComplementRowBase k b delta hk ∘ (g : Equiv.Perm (Fin (witnessComplementSize k b delta))))=
      signC (g : Equiv.Perm (Fin (witnessComplementSize k b delta))) • witnessComplementRowWord k b delta hk t := by
  rw [witness_complement_row_alternant]
  exact altWord_move _ _ g

theorem witness_complement_column_covariance (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (g : witnessComplementColumnGroup k b delta hk) :
    altWord (witnessComplementColumnGroup k b delta hk)
      (witnessComplementColumnBase k b delta hk ∘ (g : Equiv.Perm (Fin (witnessComplementSize k b delta))))=
      signC (g : Equiv.Perm (Fin (witnessComplementSize k b delta))) • witnessComplementColumnWord k b delta hk t := by
  rw [witness_complement_column_alternant]
  exact altWord_move _ _ g

end
end HSTZ
#print axioms HSTZ.witness_complement_row_fiber
#print axioms HSTZ.witness_complement_column_fiber
#print axioms HSTZ.witness_complement_row_base
#print axioms HSTZ.witness_complement_column_base
#print axioms HSTZ.witness_complement_row_alternant
#print axioms HSTZ.witness_complement_column_alternant
#print axioms HSTZ.witness_complement_row_covariance
#print axioms HSTZ.witness_complement_column_covariance
