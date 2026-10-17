import HSTZ.WitnessPreselectionClearance
import HSTZ.WitnessSelectedNonmixed

/-! For matched flag terms, pairing with the complement word equals pairing with its
low projection. This file does not prove that a common flag exists, nor that the
mismatched terms of the full target vanish. Uses `wordMap` and the coordinate
projection from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

/-- A matching single-word dual assignment pairs with the complement word exactly as
with its low projection. This is stated for the full source, before it is replaced
by independent selected factors. -/
theorem witnessComplement_matched_projection {d : ℕ} (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (ell : Fin d → Prop)
    (L : Fin d → Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)
    (hL : witnessFlagSeparated k b delta hp ell L)
    (a : Fin (witnessComplementSize k b delta) → Fin d)
    (ha : witnessFlagMatches k b delta ell a) :
    dotProduct (wordMap L (Pi.single a 1)) (witnessComplementPairWord k b delta hp.staircase_bound t)=
      dotProduct (wordMap L (Pi.single a 1))
        (witnessComplementLowProjection k b delta hp
          (witnessComplementPairWord k b delta hp.staircase_bound t)) := by
  classical
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro w hw
  rw [witnessComplementLowProjection, coordinateProjection_apply]
  change wordMap L (Pi.single a 1) w * witnessComplementPairWord k b delta hp.staircase_bound t w=
    wordMap L (Pi.single a 1) w *
      (if ∀ i, (splitLeft w i).val<2 ↔ witnessComplementPathMask k b delta i
        then witnessComplementPairWord k b delta hp.staircase_bound t w else 0)
  by_cases hm : ∀ i, (splitLeft w i).val<2 ↔ witnessComplementPathMask k b delta i
  · rw [if_pos hm]
  · rw [if_neg hm,mul_zero]
    by_cases hz : witnessComplementPairWord k b delta hp.staircase_bound t w=0
    · rw [hz,mul_zero]
    · have hs := witnessComplementPairWord_preselection_letters k b delta hp.staircase_bound t w hz
      have hn : ∃ i, ¬((splitLeft w i).val<2 ↔ witnessComplementPathMask k b delta i) := by
        simpa only [not_forall] using hm
      obtain ⟨i,hi⟩ := hn
      have hl : L (a i) (w i)=0 := by
        apply hL (a i) (w i) (hs i).1
        intro he
        exact hi (he.trans (ha i))
      rw [wordMap_single,Finset.prod_eq_zero (Finset.mem_univ i) hl,zero_mul]

end
end HSTZ
#print axioms HSTZ.witnessComplement_matched_projection
