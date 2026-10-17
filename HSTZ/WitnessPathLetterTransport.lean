import HSTZ.WitnessPathPairLetters
import HSTZ.WitnessBalanceNeighborWords
import HSTZ.WitnessBalanceTwosWords
import HSTZ.WitnessBalanceThreeWords
import HSTZ.WitnessBalanceUnmatchedWords
import OAI.RepresentationTheory.Saxl.RepeatedProjection

/-! Path pair-letter coordinates and word transport.
Reuses encoding interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Only private finite-basis packaging is added. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

private def pairLetter {d e D E : ℕ} (phi : Fin d → Fin D) (psi : Fin e → Fin E)
    (a : Fin (d*e)) : Fin (D*E) :=
  finProdFinEquiv (phi ((finProdFinEquiv : Fin d × Fin e ≃ Fin (d*e)).symm a).1,
    psi ((finProdFinEquiv : Fin d × Fin e ≃ Fin (d*e)).symm a).2)

private theorem finite_basis_sum {I : Type*} [Fintype I] [DecidableEq I] (x : I → ℂ) :
    x=∑ a : I, x a • (Pi.single (M := fun _ => ℂ) a 1) := by
  funext w
  simp [Pi.smul_apply,Pi.single_apply]

private theorem encoded_single {n d e D E : ℕ}
    (phi : Fin d → Fin D) (psi : Fin e → Fin E) (a : Fin n → Fin (d*e)) :
    encodedLetterLift phi psi (Pi.single a (1:ℂ))=
      Pi.single (pairLetter phi psi ∘ a) (1:ℂ) := by
  calc
    _ = encodedLetterLift phi psi
        (wordTensor n d e (Pi.single (splitLeft a) 1 ⊗ₜ[ℂ] Pi.single (splitRight a) 1)) := by
      rw [wordTensor_single,merge_split]
    _ = wordTensor n D E
        (Pi.single (phi ∘ splitLeft a) 1 ⊗ₜ[ℂ] Pi.single (psi ∘ splitRight a) 1) := by
      rw [encodedLetterLift_tensor,letterLift_single,letterLift_single]
    _ = _ := by
      rw [wordTensor_single]
      rfl

private theorem encoded_as_letter {n d e D E : ℕ}
    (phi : Fin d → Fin D) (psi : Fin e → Fin E) (x : WordSpace n (d*e)) :
    encodedLetterLift phi psi x=letterLift (pairLetter phi psi) x := by
  classical
  rw [finite_basis_sum x]
  change (encodedLetterLift phi psi).toLinearMap _=(letterLift _).toLinearMap _
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_smul,map_smul]
  congr 1
  exact (encoded_single phi psi a).trans (letterLift_single _ a).symm

/-- The neighboring finite-basis projection calculation, shared privately by the
neighboring and twos components. -/
private theorem letterPosition_projection {n m d D : ℕ}
    (E : Fin n ≃ Fin m) (phi : Fin d → Fin D)
    (P : (Fin m → Fin D) → Prop) (Q : (Fin n → Fin d) → Prop)
    (hp : ∀ a, P (phi ∘ a ∘ E.symm) ↔ Q a) (x : WordSpace n d) :
    coordinateProjection P (positionRelabel E (letterLift phi x))=
      positionRelabel E (letterLift phi (coordinateProjection Q x)) := by
  classical
  have he (a : Fin n → Fin d) :
      positionRelabel E (letterLift phi (Pi.single a (1:ℂ)))=
        Pi.single (phi ∘ a ∘ E.symm) (1:ℂ) := by
    rw [letterLift_single]
    funext w
    change (Pi.single (M := fun _ => ℂ) (phi ∘ a) (1:ℂ)) (w ∘ E)=
      (Pi.single (M := fun _ => ℂ) (phi ∘ a ∘ E.symm) (1:ℂ)) w
    have hw : w ∘ E=phi ∘ a ↔ w=phi ∘ a ∘ E.symm := by
      constructor
      · intro h
        funext i
        have hi := congrFun h (E.symm i)
        simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hi
      · rintro rfl
        funext i
        simp only [Function.comp_apply,Equiv.symm_apply_apply]
    simp only [Pi.single_apply,hw]
  rw [finite_basis_sum x]
  change (coordinateProjection _).comp ((positionRelabel E).toLinearMap.comp (letterLift phi).toLinearMap) _=
    ((positionRelabel E).toLinearMap.comp (letterLift phi).toLinearMap).comp (coordinateProjection _) _
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_smul,map_smul]
  congr 1
  change coordinateProjection _ (positionRelabel E (letterLift phi (Pi.single a 1)))=
    positionRelabel E (letterLift phi (coordinateProjection _ (Pi.single a 1)))
  rw [he,coordinateProjection_single,coordinateProjection_single]
  rw [hp a]
  split_ifs
  · exact (he a).symm
  · change 0=((positionRelabel E).toLinearMap.comp (letterLift phi).toLinearMap) 0
    exact (map_zero _).symm


section Witness
variable (k b delta : ℕ) (hk : 5 ≤ k)

 theorem witnessPathPairLetter_parts (a : Fin 4) :
    (finProdFinEquiv : Fin ((witnessDiagram k b delta hk).transpose.colLen 0) × Fin ((witnessDiagram k b delta hk).colLen 0) ≃ Fin (((witnessDiagram k b delta hk).transpose.colLen 0)*((witnessDiagram k b delta hk).colLen 0))).symm
      (witnessPathPairLetter k b delta hk a)=
    (witnessLowRowLetter k b delta hk ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm a).1,
      witnessLowColumnLetter k b delta hk ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm a).2) := by
  exact (finProdFinEquiv : Fin ((witnessDiagram k b delta hk).transpose.colLen 0) × Fin ((witnessDiagram k b delta hk).colLen 0) ≃ Fin (((witnessDiagram k b delta hk).transpose.colLen 0)*((witnessDiagram k b delta hk).colLen 0))).symm_apply_apply _

 theorem witnessNativePathMap_letter (x : WordSpace (witnessPathSize k) 4) :
    witnessNativePathMap k b delta hk x=letterLift (witnessPathPairLetter k b delta hk) x := by
  exact encoded_as_letter (witnessLowRowLetter k b delta hk)
    (witnessLowColumnLetter k b delta hk) x

 theorem witnessSelectedPathPairWord_letter (hp : PaperWitnessGuard k b delta) :
    witnessSelectedPathPairWord k b delta hp=
      letterLift (witnessPathPairLetter k b delta hp.staircase_bound)
        (pathPairWord ((k-2)+1)) := by
  rw [← witnessNativePathMap_generator, witnessNativePathMap_letter]
end Witness
end
end HSTZ
#print axioms HSTZ.witnessPathPairLetter_parts
#print axioms HSTZ.witnessNativePathMap_letter
#print axioms HSTZ.witnessSelectedPathPairWord_letter

/-! Neighboring component, using the private encoding/basis lemmas above. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (s : ℕ)
    (hs : 2*s+1<k-(2+delta))
include hs

theorem witnessBalanceNeighbor_encoded_letter
    (x : WordSpace (2*witnessBalanceNeighborSize (k:=k) s+1)
      ((witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0 *
       (witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0)) :
    encodedLetterLift (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs)
      (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs) x=
    letterLift (witnessBalanceNeighborPairLetter (k:=k) (b:=b) (delta:=delta) hk s hs) x :=
  encoded_as_letter _ _ x

/-- Both letters and the inverse position map commute with the local projection,
on every vector of the finite pair-word source. -/
theorem witnessBalanceNeighbor_pair_projection
    (x : WordSpace (2*witnessBalanceNeighborSize (k:=k) s+1)
      ((witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0 *
       (witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0)) :
    coordinateProjection (witnessBalanceLocalPairWords hk z (3+s))
      (positionRelabel (witnessBalanceNeighborPositions hk z s hs)
        (encodedLetterLift (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs)
          (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs) x))=
    positionRelabel (witnessBalanceNeighborPositions hk z s hs)
      (encodedLetterLift (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs)
        (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs)
        (coordinateProjection (balanceInOutputs (Set.Icc (witnessBalanceNeighborSize (k:=k) s)
          (witnessBalanceNeighborSize (k:=k) s+1))) x)) := by
  rw [witnessBalanceNeighbor_encoded_letter (k:=k) (b:=b) (delta:=delta) hk s hs,
    witnessBalanceNeighbor_encoded_letter (k:=k) (b:=b) (delta:=delta) hk s hs]
  exact letterPosition_projection (witnessBalanceNeighborPositions hk z s hs)
    (witnessBalanceNeighborPairLetter (k:=k) (b:=b) (delta:=delta) hk s hs) _ _
    (witnessBalance_neighbor_pair_filter hk z s hs) x

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceNeighbor_encoded_letter
#print axioms HSTZ.witnessBalanceNeighbor_pair_projection

/-! Twos component, keeping both letters and inverse positions. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

theorem witnessBalanceTwos_encoded_letter
    (x : WordSpace (witnessAttachment (b+1) 0).card
      ((witnessAttachment (b+1) 0).colLen 0 * (witnessAttachment (b+1) 0).colLen 0)) :
    encodedLetterLift (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk) x=
    letterLift (witnessBalanceTwosPairLetter (k:=k) (b:=b) (delta:=delta) hk) x :=
  encoded_as_letter _ _ x

/-- Projection equation for all vectors, with `E.symm` and both letters. -/
theorem witnessBalanceTwos_pair_projection
    (x : WordSpace (witnessAttachment (b+1) 0).card
      ((witnessAttachment (b+1) 0).colLen 0 * (witnessAttachment (b+1) 0).colLen 0)) :
    coordinateProjection (witnessBalanceLocalPairWords hk z 0)
      (positionRelabel (witnessBalanceTwosPositions hk z)
        (encodedLetterLift (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk)
          (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk) x))=
    positionRelabel (witnessBalanceTwosPositions hk z)
      (encodedLetterLift (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk)
        (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk)
        (coordinateProjection (balanceInOutputs ({2} : Set ℕ)) x)) := by
  rw [witnessBalanceTwos_encoded_letter (k:=k) (b:=b) (delta:=delta) hk,
    witnessBalanceTwos_encoded_letter (k:=k) (b:=b) (delta:=delta) hk]
  exact letterPosition_projection (witnessBalanceTwosPositions hk z)
    (witnessBalanceTwosPairLetter (k:=k) (b:=b) (delta:=delta) hk) _ _
    (witnessBalance_twos_pair_filter hk z) x

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceTwos_encoded_letter
#print axioms HSTZ.witnessBalanceTwos_pair_projection

/-! Height-3 component, keeping both letters and inverse positions. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 1 hk))

theorem witnessBalanceThree_encoded_letter
    (x : WordSpace 3
      ((oneRowDiagram 3).transpose.colLen 0 * (oneRowDiagram 3).transpose.colLen 0)) :
    encodedLetterLift (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk)
      (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk) x=
    letterLift (witnessBalanceThreePairLetter (k:=k) (b:=b) hk) x :=
  encoded_as_letter _ _ x

/-- Projection equation for all vectors, with `E.symm` and both letters. -/
theorem witnessBalanceThree_pair_projection
    (x : WordSpace 3
      ((oneRowDiagram 3).transpose.colLen 0 * (oneRowDiagram 3).transpose.colLen 0)) :
    coordinateProjection (witnessBalanceLocalPairWords hk z 2)
      (positionRelabel (witnessBalanceThreePositions hk z)
        (encodedLetterLift (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk)
          (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk) x))=
    positionRelabel (witnessBalanceThreePositions hk z)
      (encodedLetterLift (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk)
        (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk)
        (coordinateProjection (balanceInOutputs ({3} : Set ℕ)) x)) := by
  rw [witnessBalanceThree_encoded_letter (k:=k) (b:=b) hk,
    witnessBalanceThree_encoded_letter (k:=k) (b:=b) hk]
  exact letterPosition_projection (witnessBalanceThreePositions hk z)
    (witnessBalanceThreePairLetter (k:=k) (b:=b) hk) _ _
    (witnessBalance_three_pair_filter hk z) x

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceThree_encoded_letter
#print axioms HSTZ.witnessBalanceThree_pair_projection

/-! Unmatched singleton component, keeping both letters and inverse positions. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (s : ℕ) (hd : delta≤1) (hs : k-(2+delta)=2*s+1)

theorem witnessBalanceUnmatched_encoded_letter
    (x : WordSpace (k-2*s)
      ((oneRowDiagram (k-2*s)).transpose.colLen 0 * (oneRowDiagram (k-2*s)).transpose.colLen 0)) :
    encodedLetterLift (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs)
      (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs) x=
    letterLift (witnessBalanceUnmatchedPairLetter (k:=k) (b:=b) hk s hd hs) x :=
  encoded_as_letter _ _ x

/-- Projection equation for all vectors, with `E.symm` and both letters. -/
theorem witnessBalanceUnmatched_pair_projection
    (x : WordSpace (k-2*s)
      ((oneRowDiagram (k-2*s)).transpose.colLen 0 * (oneRowDiagram (k-2*s)).transpose.colLen 0)) :
    coordinateProjection (witnessBalanceLocalPairWords hk z (3+s))
      (positionRelabel (witnessBalanceUnmatchedPositions hk z s hd hs)
        (encodedLetterLift (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs)
          (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs) x))=
    positionRelabel (witnessBalanceUnmatchedPositions hk z s hd hs)
      (encodedLetterLift (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs)
        (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs)
        (coordinateProjection (balanceInOutputs ({k-2*s} : Set ℕ)) x)) := by
  rw [witnessBalanceUnmatched_encoded_letter (k:=k) (b:=b) hk s hd hs,
    witnessBalanceUnmatched_encoded_letter (k:=k) (b:=b) hk s hd hs]
  exact letterPosition_projection (witnessBalanceUnmatchedPositions hk z s hd hs)
    (witnessBalanceUnmatchedPairLetter (k:=k) (b:=b) hk s hd hs) _ _
    (witnessBalance_unmatched_pair_filter hk z s hd hs) x

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceUnmatched_encoded_letter
#print axioms HSTZ.witnessBalanceUnmatched_pair_projection
