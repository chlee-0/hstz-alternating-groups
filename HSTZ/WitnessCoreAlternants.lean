import HSTZ.WitnessCoreWords
import OAI.RepresentationTheory.Saxl.BandFactorization

/-! Core fiber pullback and letter-lift normalization.
Uses the fiber and `letterLift` interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This identifies only the core alternants, not the core/complement factorization
of the full witness vector or attachment support. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem witness_core_row_fiber (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    fiberGroup (fun i : Fin (staircase (k-2)).card =>
      (t ((witnessCutPositionEquiv k b delta hk t).symm (.inl i))).val.1)=
      columnGroup (transposeTableau (witnessCanonicalCore k)) := by
  ext g
  change (∀ i, (t ((witnessCutPositionEquiv k b delta hk t).symm (.inl (g i)))).val.1=
    (t ((witnessCutPositionEquiv k b delta hk t).symm (.inl i))).val.1) ↔
    (∀ i, (witnessCanonicalCore k (g i)).val.1=(witnessCanonicalCore k i).val.1)
  simp only [witnessCutPosition_core]
  rfl

theorem witness_core_column_fiber (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    fiberGroup (fun i : Fin (staircase (k-2)).card =>
      (t ((witnessCutPositionEquiv k b delta hk t).symm (.inl i))).val.2)=
      columnGroup (witnessCanonicalCore k) := by
  ext g
  change (∀ i, (t ((witnessCutPositionEquiv k b delta hk t).symm (.inl (g i)))).val.2=
    (t ((witnessCutPositionEquiv k b delta hk t).symm (.inl i))).val.2) ↔
    (∀ i, (witnessCanonicalCore k (g i)).val.2=(witnessCanonicalCore k i).val.2)
  simp only [witnessCutPosition_core]
  rfl

theorem witness_core_row_alternant (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    altWord (fiberGroup (fun i : Fin (staircase (k-2)).card =>
      (t ((witnessCutPositionEquiv k b delta hk t).symm (.inl i))).val.1))
      (fun i => rowWord (transposeTableau t)
        ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))
          ((witnessCutPositionEquiv k b delta hk t).symm (.inl i)))) =
      letterLift (witnessCoreRowLetter k b delta hk)
        (polytabloid (transposeTableau (witnessCanonicalCore k))) := by
  rw [witness_core_row_fiber,witness_core_row_word_all,
    polytabloid_eq_altWord,letterLift_altWord]

theorem witness_core_column_alternant (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    altWord (fiberGroup (fun i : Fin (staircase (k-2)).card =>
      (t ((witnessCutPositionEquiv k b delta hk t).symm (.inl i))).val.2))
      (fun i => rowWord t
        ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))
          ((witnessCutPositionEquiv k b delta hk t).symm (.inl i)))) =
      letterLift (witnessCoreColumnLetter k b delta hk)
        (polytabloid (witnessCanonicalCore k)) := by
  rw [witness_core_column_fiber,witness_core_column_word_all,
    polytabloid_eq_altWord,letterLift_altWord]

end
end HSTZ
#print axioms HSTZ.witness_core_row_fiber
#print axioms HSTZ.witness_core_column_fiber
#print axioms HSTZ.witness_core_row_alternant
#print axioms HSTZ.witness_core_column_alternant
