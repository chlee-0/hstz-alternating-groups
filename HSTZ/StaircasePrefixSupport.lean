import HSTZ.PrefixSubdiagram
import HSTZ.StaircaseContainedSupport

/-! Numeric row-prefix capacity supplies the auxiliary tableau, which feeds the
short contained four-row support theorem. Universality of the smaller core
remains an explicit embedding hypothesis. -/
namespace HSTZ
open OAI.Saxl

noncomputable def prefixSubdiagramTableau (nu : YoungDiagram) {d K : ℕ}
    (hK : K ≤ prefixSum nu.rowLen d) : Tableau K (prefixSubdiagram nu d K) :=
  canonicalTableau _ (prefixSubdiagram_card nu hK)

theorem exists_prefix_tableau (nu : YoungDiagram) {d K : ℕ}
    (hK : K ≤ prefixSum nu.rowLen d) :
    ∃ (pi : YoungDiagram) (_ : Tableau K pi),
      pi ≤ nu ∧ pi.card = K ∧ pi.colLen 0 ≤ d :=
  ⟨prefixSubdiagram nu d K, prefixSubdiagramTableau nu hK,
    prefixSubdiagram_le nu d K, prefixSubdiagram_card nu hK,
    prefixSubdiagram_rows nu d K⟩

/-- First-four-row capacity gives native target support, conditional only on
universality of the smaller core (hypothesis `hcore`), without an auxiliary band
tableau input. -/
theorem staircase_fourRow_prefix_support (h : ℕ) (hh : 1 ≤ h)
    {mu : YoungDiagram} (t : Tableau (staircase (h+2)).card mu)
    (hprefix : bandSize h 2 ≤ prefixSum mu.rowLen 4)
    (hcore : ∀ p : Nat.Partition (staircase h).card,
      ∃ f : Representation.IntertwiningMap (spechtRep (partitionTableau p))
        (cyclicSubrepresentation (wordRep _ _) (staircaseWord h)).toRepresentation,
        Function.Injective f) :
    ∃ E : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic (h+2)).toRepresentation, Function.Injective E := by
  exact staircase_contained_fourRow_support h hh
    (prefixSubdiagramTableau mu hprefix) t
    (prefixSubdiagram_rows mu 4 (bandSize h 2))
    (prefixSubdiagram_le mu 4 (bandSize h 2)) hcore

end HSTZ
#print axioms HSTZ.exists_prefix_tableau
#print axioms HSTZ.staircase_fourRow_prefix_support
