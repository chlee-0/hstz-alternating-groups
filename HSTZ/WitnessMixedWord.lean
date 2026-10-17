import HSTZ.WitnessMaskProjection
import OAI.RepresentationTheory.Saxl.SignEquivalence

/-! The paired polytabloid word of the transpose and original tableaux, in unequal
alphabets. Uses `wordTensor` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessMixedWord (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    WordSpace n ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) :=
  wordTensor n _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ] polytabloid t)

theorem witnessMixedWord_coordinate (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk))
    (w : Fin n → Fin ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0)) :
    witnessMixedWord k b delta hk t w =
      polytabloid (transposeTableau t) (splitLeft w) * polytabloid t (splitRight w) :=
  wordTensor_tmul _ _ _

theorem witnessMixedWord_alphabets (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessDiagram k b delta hk).transpose.colLen 0=k+b+delta ∧
    (witnessDiagram k b delta hk).colLen 0=k := by
  exact ⟨by rw [YoungDiagram.colLen_transpose,witnessDiagram_width],
    witnessDiagram_height k b delta hk⟩

end
end HSTZ
#print axioms HSTZ.witnessMixedWord_coordinate
#print axioms HSTZ.witnessMixedWord_alphabets
