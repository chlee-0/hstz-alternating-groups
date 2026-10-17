import HSTZ.WitnessBinaryCut
import HSTZ.WitnessRetainedPair

/-! Rotated path coordinates under the original asymmetric witness cut.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Separate width and height alphabets and the relocated endpoint are kept; no native binary
path or independent path/attachment tensor is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

abbrev witnessPathEndpoint (k : ℕ) : Fin (witnessPathSize k) :=
  ⟨2*((k-2)+1),by change 2*((k-2)+1)<2*((k-2)+1)+1; omega⟩

theorem witnessPathPositionCell_coordinates (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) :
    (witnessPathPositionCell k b delta hk i).val=
      ((k-2)+1-(i.val+1)/2,
        if i.val/2=k-1 then k+b+delta-1 else i.val/2) := rfl

def witnessPathRowBase (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) : Fin ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  let x := witnessRowRotation k b delta hk (witnessPathPositionCell k b delta hk i)
  ⟨x.val.2,by
    rw [YoungDiagram.colLen_transpose]
    exact YoungDiagram.mem_iff_lt_rowLen.mp
      ((witnessDiagram k b delta hk).up_left_mem (Nat.zero_le _) le_rfl x.property)⟩

def witnessPathColumnBase (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) : Fin ((witnessDiagram k b delta hk).colLen 0) :=
  let x := witnessColumnRotation k b delta hk (witnessPathPositionCell k b delta hk i)
  ⟨x.val.1,YoungDiagram.mem_iff_lt_colLen.mp
    ((witnessDiagram k b delta hk).up_left_mem le_rfl (Nat.zero_le _) x.property)⟩

def witnessPathRowRestriction (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    Fin (witnessPathSize k) → Fin ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  fun i => rowWord (transposeTableau t)
    ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))
      ((witnessBinaryCut k b delta hk t).symm
        (.inr (witnessComplementOrder k b delta (.inl i)))))

def witnessPathColumnRestriction (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    Fin (witnessPathSize k) → Fin ((witnessDiagram k b delta hk).colLen 0) :=
  fun i => rowWord t
    ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))
      ((witnessBinaryCut k b delta hk t).symm
        (.inr (witnessComplementOrder k b delta (.inl i)))))

theorem witness_path_row_restriction (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessPathRowRestriction k b delta hk t=witnessPathRowBase k b delta hk := by
  funext i
  apply Fin.ext
  change (t ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))
    ((witnessBinaryCut k b delta hk t).symm
      (.inr (witnessComplementOrder k b delta (.inl i)))))).val.2=_
  rw [witnessRowRotationPositions_cell,witnessBinaryCut_path,witnessCutPosition_path]
  rfl

theorem witness_path_column_restriction (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessPathColumnRestriction k b delta hk t=witnessPathColumnBase k b delta hk := by
  funext i
  apply Fin.ext
  change (t ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))
    ((witnessBinaryCut k b delta hk t).symm
      (.inr (witnessComplementOrder k b delta (.inl i)))))).val.1=_
  rw [witnessColumnRotationPositions_cell,witnessBinaryCut_path,witnessCutPosition_path]
  rfl

theorem witnessPathRowBase_value (k b delta : ℕ) (hk : 5 ≤ k) (i : Fin (witnessPathSize k)) :
    (witnessPathRowBase k b delta hk i).val=
      witnessRowForward k b ((k-2)+1-(i.val+1)/2)
        (if i.val/2=k-1 then k+b+delta-1 else i.val/2) := rfl

theorem witnessPathColumnBase_value (k b delta : ℕ) (hk : 5 ≤ k) (i : Fin (witnessPathSize k)) :
    (witnessPathColumnBase k b delta hk i).val=
      if (k-2)+1-(i.val+1)/2 < k-2-(if i.val/2=k-1 then k+b+delta-1 else i.val/2)
      then (k-2)+1-(i.val+1)/2+2
      else ((k-2)+1-(i.val+1)/2)-(k-2-(if i.val/2=k-1 then k+b+delta-1 else i.val/2)) := rfl

theorem witnessPathRowBase_endpoint (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessPathRowBase k b delta hk (witnessPathEndpoint k)).val=
      witnessFirstRowForward k b (k+b+delta-1) := by
  change witnessRowForward k b
    (witnessPathPositionCell k b delta hk (witnessPathEndpoint k)).val.1
    (witnessPathPositionCell k b delta hk (witnessPathEndpoint k)).val.2=_
  rw [witnessPathPositionCell_endpoint]
  rfl

theorem witnessPathColumnBase_endpoint (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessPathColumnBase k b delta hk (witnessPathEndpoint k)).val=0 := by
  change (if (witnessPathPositionCell k b delta hk (witnessPathEndpoint k)).val.1<
    k-2-(witnessPathPositionCell k b delta hk (witnessPathEndpoint k)).val.2
    then (witnessPathPositionCell k b delta hk (witnessPathEndpoint k)).val.1+2
    else (witnessPathPositionCell k b delta hk (witnessPathEndpoint k)).val.1-
      (k-2-(witnessPathPositionCell k b delta hk (witnessPathEndpoint k)).val.2))=0
  rw [witnessPathPositionCell_endpoint]
  have he : k-2-(k+b+delta-1)=0 := by omega
  simp only [he,Nat.not_lt_zero,if_false,Nat.sub_zero]

end
end HSTZ
#print axioms HSTZ.witnessPathPositionCell_coordinates
#print axioms HSTZ.witness_path_row_restriction
#print axioms HSTZ.witness_path_column_restriction
#print axioms HSTZ.witnessPathRowBase_value
#print axioms HSTZ.witnessPathColumnBase_value
#print axioms HSTZ.witnessPathRowBase_endpoint
#print axioms HSTZ.witnessPathColumnBase_endpoint
