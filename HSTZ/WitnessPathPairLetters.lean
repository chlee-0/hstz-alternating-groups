import HSTZ.WitnessNativePath

/-! Embedding of the four path letters into the unequal witness width and height
alphabets. Uses tensor and letter interfaces adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). Only private coordinate packaging
is added here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessPathPairLetter (k b delta : ℕ) (hk : 5 ≤ k) :
    Fin 4 ↪ Fin ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) :=
  (((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm.toEmbedding).trans
    (Function.Embedding.prodMap (witnessLowRowLetter k b delta hk)
      (witnessLowColumnLetter k b delta hk))).trans
    (finProdFinEquiv : Fin ((witnessDiagram k b delta hk).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hk).colLen 0) ≃ Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0 *
        (witnessDiagram k b delta hk).colLen 0)).toEmbedding

theorem witnessPathPairLetter_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessPathPairLetter k b delta hk) :=
  (witnessPathPairLetter k b delta hk).injective
end
end HSTZ
#print axioms HSTZ.witnessPathPairLetter
#print axioms HSTZ.witnessPathPairLetter_injective
