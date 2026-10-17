import HSTZ.WitnessBinaryCut
import HSTZ.WitnessCoreAlternants
import HSTZ.WitnessRetainedPair
import HSTZ.PositionLayer

/-! Retained-layer and paired core/complement factorization for the original
asymmetric witness tableau. Uses the `fiberSplit`, `altWord_fiber_split` and
`letterLift` interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The full complement fiber groups are kept. No path/attachment tensor split,
staircase-generator transport or global shuffle is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

theorem witness_full_row_fiber (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    columnGroup (transposeTableau t)=fiberGroup (fun i => (t i).val.1) := rfl

theorem witness_full_column_fiber (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    columnGroup t=fiberGroup (fun i => (t i).val.2) := rfl

theorem witnessBinaryCut_sector (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    sectorGroup (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk t))=
      sectorGroup (fun i => (witnessBinaryCut k b delta hk t i).isLeft=true) := by
  congr 1
  funext i
  exact propext (witnessBinaryCut_mask k b delta hk t i).symm

def witnessComplementRowWord (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    WordSpace (witnessComplementSize k b delta) ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  altWord (fiberGroup (fun i => (t ((witnessBinaryCut k b delta hk t).symm (.inr i))).val.1))
    (rightWord (witnessBinaryCut k b delta hk t)
      (rowWord (transposeTableau t) ∘ (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))))

def witnessComplementColumnWord (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    WordSpace (witnessComplementSize k b delta) ((witnessDiagram k b delta hk).colLen 0) :=
  altWord (fiberGroup (fun i => (t ((witnessBinaryCut k b delta hk t).symm (.inr i))).val.2))
    (rightWord (witnessBinaryCut k b delta hk t)
      (rowWord t ∘ (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))))

theorem witness_retained_row_factor (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessRetainedRowWord k b delta hk t =
      positionProduct (witnessBinaryCut k b delta hk t)
        (letterLift (witnessCoreRowLetter k b delta hk)
          (polytabloid (transposeTableau (witnessCanonicalCore k))))
        (witnessComplementRowWord k b delta hk t) := by
  unfold witnessRetainedRowWord
  change altWord (fiberGroup (fun i => (t i).val.1) ⊓
    sectorGroup (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk t)))
    (rowWord (transposeTableau t) ∘ (witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n)))=_
  rw [witnessBinaryCut_sector,altWord_fiber_split]
  have hc := witness_core_row_alternant k b delta hk t
  simp only [← witnessBinaryCut_core k b delta hk t] at hc
  exact congrArg (fun v => positionProduct (witnessBinaryCut k b delta hk t) v
      (witnessComplementRowWord k b delta hk t)) hc

theorem witness_retained_column_factor (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessRetainedColumnWord k b delta hk t =
      positionProduct (witnessBinaryCut k b delta hk t)
        (letterLift (witnessCoreColumnLetter k b delta hk)
          (polytabloid (witnessCanonicalCore k)))
        (witnessComplementColumnWord k b delta hk t) := by
  unfold witnessRetainedColumnWord
  change altWord (fiberGroup (fun i => (t i).val.2) ⊓
    sectorGroup (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk t)))
    (rowWord t ∘ (witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n)))=_
  rw [witnessBinaryCut_sector,altWord_fiber_split]
  have hc := witness_core_column_alternant k b delta hk t
  simp only [← witnessBinaryCut_core k b delta hk t] at hc
  exact congrArg (fun v => positionProduct (witnessBinaryCut k b delta hk t) v
      (witnessComplementColumnWord k b delta hk t)) hc

def witnessEmbeddedCorePair (k b delta : ℕ) (hk : 5 ≤ k) :
    WordSpace (staircase (k-2)).card
      ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0) :=
  wordTensor _ _ _
    (letterLift (witnessCoreRowLetter k b delta hk) (polytabloid (transposeTableau (witnessCanonicalCore k))) ⊗ₜ[ℂ]
      letterLift (witnessCoreColumnLetter k b delta hk) (polytabloid (witnessCanonicalCore k)))

def witnessComplementPairWord (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    WordSpace (witnessComplementSize k b delta)
      ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0) :=
  wordTensor _ _ _ (witnessComplementRowWord k b delta hk t ⊗ₜ[ℂ]
    witnessComplementColumnWord k b delta hk t)

theorem witness_retained_pair_factor (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessRetainedPairWord k b delta hk t=
      positionProduct (witnessBinaryCut k b delta hk t)
        (witnessEmbeddedCorePair k b delta hk) (witnessComplementPairWord k b delta hk t) := by
  unfold witnessRetainedPairWord
  rw [witness_retained_row_factor,witness_retained_column_factor,wordTensor_positionProduct]
  rfl

theorem witness_filtered_core_factor (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk t)=
      witnessRotationPhase k b delta hk t •
        positionProduct (witnessBinaryCut k b delta hk t)
          (witnessEmbeddedCorePair k b delta hk) (witnessComplementPairWord k b delta hk t) := by
  rw [witness_filtered_retained_pair,witness_retained_pair_factor]

theorem witnessComplementPairWord_ne_zero (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) : witnessComplementPairWord k b delta hk t≠0 := by
  intro hz
  have he := witness_retained_pair_factor k b delta hk t
  rw [hz] at he
  have hp : positionProduct (witnessBinaryCut k b delta hk t)
      (witnessEmbeddedCorePair k b delta hk) 0=0 := by
    funext w
    exact mul_zero _
  rw [hp] at he
  exact witnessRetainedPairWord_ne_zero k b delta hk t he

end
end HSTZ
#print axioms HSTZ.witness_full_row_fiber
#print axioms HSTZ.witness_full_column_fiber
#print axioms HSTZ.witnessBinaryCut_sector
#print axioms HSTZ.witness_retained_row_factor
#print axioms HSTZ.witness_retained_column_factor
#print axioms HSTZ.witness_retained_pair_factor
#print axioms HSTZ.witness_filtered_core_factor
#print axioms HSTZ.witnessComplementPairWord_ne_zero
