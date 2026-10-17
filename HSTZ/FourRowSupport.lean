import HSTZ.PathCoefficients
import OAI.RepresentationTheory.Saxl.BandPairing

/-! Four-row Specht embeddings from the native tableau contraction.
The native bound r ≥ 2 and the resulting bound h ≥ 1 are kept. The nonzero contraction
is proved, not assumed. The band position-group pullback is explicit. -/
namespace HSTZ

/-- A tableau vector and a letter matrix with nonzero paired-path contraction. -/
theorem fourRow_pathPair_contraction (r : ℕ) (_hr : 2 ≤ r) {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau (2*r+1) mu) (hmu : mu.colLen 0 ≤ 4) :
    ∃ x : (OAI.Saxl.spechtSub t).toSubmodule,
      ∃ L : Fin (mu.colLen 0) → Fin 4 → ℂ,
        dotProduct (OAI.Saxl.wordMap L x.val) (pathPairWord r) ≠ 0 := by
  have hn : mu.transpose.rowLens.sum = 2*r+1 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr ((OAI.Saxl.Columns.columnTableau mu).trans t.symm)
  obtain ⟨s, hs⟩ := OAI.Saxl.Path.fourRow_tableau_noncancellation (2*r+1) mu hn hmu
  let L : Fin (mu.colLen 0) → Fin 4 → ℂ := fun i a =>
    OAI.Saxl.Band.conjugation (OAI.Saxl.Band.basis i.val)
      (OAI.Saxl.Path.parts a).1 (OAI.Saxl.Path.parts a).2
  have hnative : dotProduct (OAI.Saxl.wordMap L (OAI.Saxl.polytabloid s))
      (OAI.Saxl.Path.bandWord r) ≠ 0 := by
    intro hz
    rw [OAI.Saxl.Path.chainFunctional_endpoint] at hs
    apply hs
    change (-1 : ℂ)^r * dotProduct (OAI.Saxl.wordMap L (OAI.Saxl.polytabloid s))
      (OAI.Saxl.Path.bandWord r) = 0
    rw [hz, mul_zero]
  refine ⟨⟨OAI.Saxl.polytabloid s, OAI.Saxl.polytabloid_mem_all t s⟩, L, ?_⟩
  rw [pathPairWord_eq_signed, dotProduct_smul, smul_eq_mul]
  exact mul_ne_zero (pow_ne_zero r (by norm_num)) hnative

/-- Every four-row Specht module of odd size at least 5 embeds into the prescribed path. -/
theorem fourRow_pathPair_embedding (r : ℕ) (hr : 2 ≤ r) {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau (2*r+1) mu) (hmu : mu.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (OAI.Saxl.cyclic (OAI.Saxl.wordRep _ 4) (pathPairWord r)).toRepresentation,
      Function.Injective F := by
  obtain ⟨x, L, hnz⟩ := fourRow_pathPair_contraction r hr t hmu
  exact pathPairWord_contraction_embedding r t x L hnz

/-- Four-row embedding into the s = 2 band cyclic space after the named
position-group pullback. -/
theorem fourRow_band_embedding (h : ℕ) (hh : 1 ≤ h) {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau (2*(h+1)+1) mu) (hmu : mu.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (pathBandRepresentation h) (bandPairWord h 2)).toRepresentation,
      Function.Injective F := by
  obtain ⟨x, L, hnz⟩ := fourRow_pathPair_contraction (h+1) (by omega) t hmu
  exact bandPath_contraction_embedding h t x L hnz

end HSTZ
#print axioms HSTZ.fourRow_pathPair_contraction
#print axioms HSTZ.fourRow_pathPair_embedding
#print axioms HSTZ.fourRow_band_embedding
