import HSTZ.WitnessRowRotation
import HSTZ.WitnessFilteredCore

/-! Row rotation under the original witness tableau. The retained row layer follows
the `altWord_sector_rotated` interface from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Its sign is kept explicit and not identified with the global kappa. -/
namespace HSTZ
open OAI.Saxl

noncomputable def witnessRowRotationPositions (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) : columnGroup (transposeTableau t) :=
  ⟨(t.trans (witnessRowRotation k b delta hk)).trans t.symm,by
    intro i
    change (t (t.symm (witnessRowRotation k b delta hk (t i)))).val.1=(t i).val.1
    rw [t.apply_symm_apply]
    exact witnessRowRotation_row k b delta hk (t i)⟩

theorem witnessRowRotationPositions_cell (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) :
    t ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)) i)=
      witnessRowRotation k b delta hk (t i) := t.apply_symm_apply _

theorem witnessRowRotationPositions_marked (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) :
    witnessRowMarked k b
      (rowWord (transposeTableau t) ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)) i)).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t) := by
  change witnessRowMarked k b
    (t ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)) i)).val.2 ↔ _
  rw [witnessRowRotationPositions_cell]
  exact (witnessRowRotation_marked k b delta hk (t i)).trans
    ((witnessCoreCell_range k b delta hk (t i)).symm.trans
      (witnessCorePositionEmbedding_range k b delta hk t i).symm)

noncomputable def witnessRetainedRowWord (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    WordSpace n ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  altWord (columnGroup (transposeTableau t) ⊓ sectorGroup
    (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk t)))
    (rowWord (transposeTableau t) ∘ (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)))

theorem witness_projected_row_layer (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    coordinateProjection (fun a => ∀ i, witnessRowMarked k b (a i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t)) (polytabloid (transposeTableau t)) =
    signC (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)) •
      witnessRetainedRowWord k b delta hk t := by
  exact altWord_sector_rotated (columnGroup (transposeTableau t)) (rowWord (transposeTableau t))
    (fun a => witnessRowMarked k b a.val)
    (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk t))
    (witnessRowRotationPositions k b delta hk t)
    (witnessRowRotationPositions_marked k b delta hk t)


theorem witnessRowRotationPositions_inverse_cell (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) :
    t ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))⁻¹ i)=
      (witnessRowRotation k b delta hk).symm (t i) := by
  change t (t.symm ((witnessRowRotation k b delta hk).symm (t i)))=_
  exact t.apply_symm_apply _

theorem witness_projected_row_coefficient (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    coordinateProjection (fun a => ∀ i, witnessRowMarked k b (a i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t)) (polytabloid (transposeTableau t))
      (rowWord (transposeTableau t) ∘ (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))) =
    signC (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)) := by
  classical
  rw [coordinateProjection_apply]
  split_ifs with h
  · exact polytabloid_column_coeff (transposeTableau t) (witnessRowRotationPositions k b delta hk t)
  · exact False.elim (h (fun i => witnessRowRotationPositions_marked k b delta hk t i))

theorem witnessRetainedRowWord_coefficient (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessRetainedRowWord k b delta hk t
      (rowWord (transposeTableau t) ∘ (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)))=1 := by
  let g : Equiv.Perm (Fin n) := witnessRowRotationPositions k b delta hk t
  let a := rowWord (transposeTableau t) ∘ g
  have he := congrFun (witness_projected_row_layer k b delta hk t) a
  rw [witness_projected_row_coefficient] at he
  change signC g = signC g * witnessRetainedRowWord k b delta hk t a at he
  change witnessRetainedRowWord k b delta hk t a=1
  calc
    _ = signC g * (signC g * witnessRetainedRowWord k b delta hk t a) := by
      rw [← mul_assoc,signC_mul_self,one_mul]
    _ = signC g * signC g := by rw [← he]
    _ = 1 := signC_mul_self g

theorem witnessRetainedRowWord_ne_zero (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessRetainedRowWord k b delta hk t ≠ 0 := by
  intro hz
  have he := witnessRetainedRowWord_coefficient k b delta hk t
  rw [hz] at he
  exact zero_ne_one he

end HSTZ
#print axioms HSTZ.witnessRowRotationPositions
#print axioms HSTZ.witnessRowRotationPositions_cell
#print axioms HSTZ.witnessRowRotationPositions_marked
#print axioms HSTZ.witness_projected_row_layer
#print axioms HSTZ.witnessRowRotationPositions_inverse_cell
#print axioms HSTZ.witness_projected_row_coefficient
#print axioms HSTZ.witnessRetainedRowWord_coefficient
#print axioms HSTZ.witnessRetainedRowWord_ne_zero
