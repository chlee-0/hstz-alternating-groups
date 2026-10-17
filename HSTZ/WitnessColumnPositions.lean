import HSTZ.WitnessColumnRotation
import HSTZ.WitnessFilteredCore

/-! Column rotation under the original witness tableau. The column layer follows
the `altWord_sector_rotated` interface of OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Its sign is kept and is not identified with the global kappa. -/
namespace HSTZ
open OAI.Saxl

noncomputable def witnessColumnRotationPositions (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) : columnGroup t :=
  ⟨(t.trans (witnessColumnRotation k b delta hk)).trans t.symm,by
    intro i
    change (t (t.symm (witnessColumnRotation k b delta hk (t i)))).val.2=(t i).val.2
    rw [t.apply_symm_apply]
    exact witnessColumnRotation_column k b delta hk (t i)⟩

theorem witnessColumnRotationPositions_cell (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) :
    t ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n)) i)=
      witnessColumnRotation k b delta hk (t i) := t.apply_symm_apply _

theorem witnessColumnRotationPositions_marked (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) :
    witnessColumnMarked k
      (rowWord t ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n)) i)).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t) := by
  change witnessColumnMarked k
    (t ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n)) i)).val.1 ↔ _
  rw [witnessColumnRotationPositions_cell]
  exact (witnessColumnRotation_marked k b delta hk (t i)).trans
    ((witnessCoreCell_range k b delta hk (t i)).symm.trans
      (witnessCorePositionEmbedding_range k b delta hk t i).symm)

noncomputable def witnessRetainedColumnWord (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    WordSpace n ((witnessDiagram k b delta hk).colLen 0) :=
  altWord (columnGroup t ⊓ sectorGroup
    (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk t)))
    (rowWord t ∘ (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n)))

theorem witness_projected_column_layer (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    coordinateProjection (fun a => ∀ i, witnessColumnMarked k (a i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t)) (polytabloid t) =
    signC (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n)) •
      witnessRetainedColumnWord k b delta hk t := by
  exact altWord_sector_rotated (columnGroup t) (rowWord t)
    (fun a => witnessColumnMarked k a.val)
    (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk t))
    (witnessColumnRotationPositions k b delta hk t)
    (witnessColumnRotationPositions_marked k b delta hk t)


theorem witnessColumnRotationPositions_inverse_cell (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) :
    t ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))⁻¹ i)=
      (witnessColumnRotation k b delta hk).symm (t i) := by
  change t (t.symm ((witnessColumnRotation k b delta hk).symm (t i)))=_
  exact t.apply_symm_apply _

theorem witness_projected_column_coefficient (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    coordinateProjection (fun a => ∀ i, witnessColumnMarked k (a i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t)) (polytabloid t)
      (rowWord t ∘ (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))) =
    signC (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n)) := by
  classical
  rw [coordinateProjection_apply]
  split_ifs with h
  · exact polytabloid_column_coeff t (witnessColumnRotationPositions k b delta hk t)
  · exact False.elim (h (fun i => witnessColumnRotationPositions_marked k b delta hk t i))

theorem witnessRetainedColumnWord_coefficient (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessRetainedColumnWord k b delta hk t
      (rowWord t ∘ (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n)))=1 := by
  let g : Equiv.Perm (Fin n) := witnessColumnRotationPositions k b delta hk t
  let a := rowWord t ∘ g
  have he := congrFun (witness_projected_column_layer k b delta hk t) a
  rw [witness_projected_column_coefficient] at he
  change signC g = signC g * witnessRetainedColumnWord k b delta hk t a at he
  change witnessRetainedColumnWord k b delta hk t a=1
  calc
    _ = signC g * (signC g * witnessRetainedColumnWord k b delta hk t a) := by
      rw [← mul_assoc,signC_mul_self,one_mul]
    _ = signC g * signC g := by rw [← he]
    _ = 1 := signC_mul_self g

theorem witnessRetainedColumnWord_ne_zero (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessRetainedColumnWord k b delta hk t ≠ 0 := by
  intro hz
  have he := witnessRetainedColumnWord_coefficient k b delta hk t
  rw [hz] at he
  exact zero_ne_one he

end HSTZ
#print axioms HSTZ.witnessColumnRotationPositions
#print axioms HSTZ.witnessColumnRotationPositions_cell
#print axioms HSTZ.witnessColumnRotationPositions_marked
#print axioms HSTZ.witness_projected_column_layer
#print axioms HSTZ.witnessColumnRotationPositions_inverse_cell
#print axioms HSTZ.witness_projected_column_coefficient
#print axioms HSTZ.witnessRetainedColumnWord_coefficient
#print axioms HSTZ.witnessRetainedColumnWord_ne_zero
