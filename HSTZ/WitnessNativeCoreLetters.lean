import HSTZ.WitnessCoreAlternants
import HSTZ.LetterLift

/-! The alphabet and generator bridge between native staircase rows and the
transpose core. The proofs are new and use interfaces adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). The alphabet embeddings allow
unequal alphabets and keep the position enumeration, with no global shuffle phase. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

/-- Equivalence of equal-size alphabets, from the staircase dimensions. -/
def staircaseTransposeAlphabet (m : ℕ) :
    Fin ((staircase m).colLen 0) ≃ Fin ((staircase m).transpose.colLen 0) :=
  finCongr (by simp only [YoungDiagram.colLen_transpose,staircase_row_length,staircase_colLen,Nat.sub_zero])

theorem staircaseTransposeAlphabet_value (m : ℕ) (i : Fin ((staircase m).colLen 0)) :
    (staircaseTransposeAlphabet m i).val=i.val := rfl

def witnessNativeCoreRowLetter (k b delta : ℕ) (hk : 5 ≤ k) :
    Fin ((staircase (k-2)).colLen 0) → Fin ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  witnessCoreRowLetter k b delta hk ∘ staircaseTransposeAlphabet (k-2)

theorem witnessNativeCoreRowLetter_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessNativeCoreRowLetter k b delta hk) :=
  (witnessCoreRowLetter_injective k b delta hk).comp (staircaseTransposeAlphabet (k-2)).injective

theorem witnessNativeCoreRowLetter_value (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin ((staircase (k-2)).colLen 0)) :
    (witnessNativeCoreRowLetter k b delta hk i).val=
      if i.val=k-3 then k+b-1 else i.val+2 := rfl

theorem witness_native_core_tableau (k : ℕ) : witnessCanonicalCore k=stairTableau (k-2) := rfl

theorem witness_native_core_row_fiber (k : ℕ) :
    columnGroup (stairRowTableau (k-2))=
      columnGroup (transposeTableau (witnessCanonicalCore k)) := rfl

theorem witness_native_core_row_word (k b delta : ℕ) (hk : 5 ≤ k) :
    witnessNativeCoreRowLetter k b delta hk ∘ rowWord (stairRowTableau (k-2))=
      witnessCoreRowLetter k b delta hk ∘ rowWord (transposeTableau (witnessCanonicalCore k)) := by
  funext i
  apply congrArg (witnessCoreRowLetter k b delta hk)
  apply Fin.ext
  rfl

theorem witness_native_core_row_polytabloid (k b delta : ℕ) (hk : 5 ≤ k) :
    letterLift (witnessNativeCoreRowLetter k b delta hk) (polytabloid (stairRowTableau (k-2)))=
      letterLift (witnessCoreRowLetter k b delta hk)
        (polytabloid (transposeTableau (witnessCanonicalCore k))) := by
  simp only [polytabloid_eq_altWord,letterLift_altWord,witness_native_core_row_fiber,
    witness_native_core_row_word]

end
end HSTZ
#print axioms HSTZ.staircaseTransposeAlphabet_value
#print axioms HSTZ.witnessNativeCoreRowLetter_injective
#print axioms HSTZ.witnessNativeCoreRowLetter_value
#print axioms HSTZ.witness_native_core_tableau
#print axioms HSTZ.witness_native_core_row_fiber
#print axioms HSTZ.witness_native_core_row_word
#print axioms HSTZ.witness_native_core_row_polytabloid
