import HSTZ.WitnessRowPositions
import HSTZ.WitnessColumnPositions

/-! The retained paired witness word and its signed filtered identity. The
composition is new and uses tensor and sector interfaces adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). The rotation phase is the
product of the permutation signs, not an asserted global shuffle sign. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessRetainedPairWord (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    WordSpace n ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) :=
  wordTensor n _ _ (witnessRetainedRowWord k b delta hk t ⊗ₜ[ℂ]
    witnessRetainedColumnWord k b delta hk t)

def witnessRotationPhase (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) : ℂ :=
  signC (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)) *
    signC (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))

theorem witnessRotationPhase_sq (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessRotationPhase k b delta hk t * witnessRotationPhase k b delta hk t=1 := by
  unfold witnessRotationPhase
  rw [mul_mul_mul_comm,signC_mul_self,signC_mul_self,one_mul]

theorem witnessRotationPhase_ne_zero (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) : witnessRotationPhase k b delta hk t≠0 := by
  intro hz
  have he:=witnessRotationPhase_sq k b delta hk t
  rw [hz,zero_mul] at he
  exact zero_ne_one he

theorem witness_filtered_retained_pair (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk t)=
      witnessRotationPhase k b delta hk t • witnessRetainedPairWord k b delta hk t := by
  rw [witness_filtered_sector_tensor,witness_projected_row_layer,witness_projected_column_layer]
  unfold witnessRotationPhase witnessRetainedPairWord
  rw [TensorProduct.smul_tmul_smul,map_smul]

theorem witnessRetainedPairWord_coefficient (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessRetainedPairWord k b delta hk t
      (mergeWords
        (rowWord (transposeTableau t) ∘ (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)))
        (rowWord t ∘ (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))))=1 := by
  unfold witnessRetainedPairWord
  rw [wordTensor_tmul,splitLeft_merge,splitRight_merge,
    witnessRetainedRowWord_coefficient,witnessRetainedColumnWord_coefficient,one_mul]

theorem witnessRetainedPairWord_ne_zero (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) : witnessRetainedPairWord k b delta hk t≠0 := by
  intro hz
  have he:=witnessRetainedPairWord_coefficient k b delta hk t
  rw [hz] at he
  exact zero_ne_one he

theorem witness_filtered_retained_coefficient (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk t)
      (mergeWords
        (rowWord (transposeTableau t) ∘ (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)))
        (rowWord t ∘ (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))))=
      witnessRotationPhase k b delta hk t := by
  rw [witness_filtered_retained_pair]
  change witnessRotationPhase k b delta hk t * witnessRetainedPairWord k b delta hk t _=_
  rw [witnessRetainedPairWord_coefficient,mul_one]

theorem witness_filtered_mixed_ne_zero (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk t)≠0 := by
  intro hz
  have he:=witness_filtered_retained_coefficient k b delta hk t
  rw [hz] at he
  exact witnessRotationPhase_ne_zero k b delta hk t he.symm

end
end HSTZ
#print axioms HSTZ.witnessRotationPhase_sq
#print axioms HSTZ.witnessRotationPhase_ne_zero
#print axioms HSTZ.witness_filtered_retained_pair
#print axioms HSTZ.witnessRetainedPairWord_coefficient
#print axioms HSTZ.witnessRetainedPairWord_ne_zero
#print axioms HSTZ.witness_filtered_retained_coefficient
#print axioms HSTZ.witness_filtered_mixed_ne_zero
