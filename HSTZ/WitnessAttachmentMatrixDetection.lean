import HSTZ.WordMapSpan
import HSTZ.WitnessAttachmentBilinearDetection

/-! Attachment matrix detection for some position translate. Uses `wordMap` and
Specht interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
No fixed placement, replacement of the contained carrier, or common basis is
asserted. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem wordMap_pair_detect {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (x : WordSpace n d) (u : WordSpace n e)
    (hF : dotProduct (F x) u ≠ 0) :
    ∃ L : Fin d → Fin e → ℂ, dotProduct (wordMap L x) u ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hz : ∀ f ∈ Submodule.span ℂ
      (Set.range (fun L : Fin d → Fin e → ℂ => wordMap (n := n) L)),
      dotProduct (f x) u = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨L,rfl⟩ := hf; exact h L
    | zero => change dotProduct 0 u = 0; exact zero_dotProduct u
    | add f g hf hg ihf ihg =>
      change dotProduct (f x + g x) u = 0
      rw [add_dotProduct,ihf,ihg,add_zero]
    | smul c f hf ih =>
      change dotProduct (c • f x) u = 0
      rw [smul_dotProduct,ih,smul_zero]
  exact hF (hz F (wordIntertwiner_mem_wordMap_span F))

/-- Some position translate of the prescribed original polytabloid has a
nonzero rectangular `wordMap` matrix coefficient against the selected attachment
source. No common or nondegenerate flag is asserted. -/
theorem witnessSelectedAttachment_matrix_translate_pair (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b delta).card mu)
    (hc : ColumnParity mu.colLen delta) (ht : mu.rowLen 0 ≤ 4) :
    ∃ sigma : Equiv.Perm (Fin (witnessAttachment b delta).card),
      ∃ L : Fin (mu.colLen 0) →
        Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
          (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ,
      dotProduct (wordMap L (wordRep _ _ sigma.symm (polytabloid t)))
        (witnessSelectedAttachmentPairWord k b delta hp) ≠ 0 := by
  obtain ⟨G,sigma,hpair⟩ :=
    witnessSelectedAttachment_ambient_translate_pair k b delta hp t hc ht
  obtain ⟨L,hL⟩ := wordMap_pair_detect G _ _ hpair
  exact ⟨sigma,L,hL⟩
end
end HSTZ
#print axioms HSTZ.witnessSelectedAttachment_matrix_translate_pair
