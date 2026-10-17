import HSTZ.YoungDiagramCompat
import HSTZ.StaircaseDominatedSupport
import HSTZ.StaircaseLongRowSupport
import HSTZ.StaircaseDominanceSupport

/-! Universality of the native prescribed staircase cyclic space. This combines
the dominated embeddings, the one-step long-row embeddings and the two-step
short-row/non-dominated embeddings. The short case uses the contained four-row
completion. -/
namespace HSTZ
open OAI.Saxl

/-- Every tableau of staircase degree has a Specht injection into the native
prescribed staircase cyclic space, including `m = 0`. -/
theorem staircase_universal_embedding (m : ℕ) :
    ∀ (mu : YoungDiagram) (t : Tableau (staircase m).card mu),
      ∃ E : Representation.IntertwiningMap (spechtRep t)
        (staircaseCyclic m).toRepresentation, Function.Injective E := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro mu t
    by_cases hd : Dominates (staircase m) mu
    · exact staircase_dominated_embedding m mu t hd
    have hsize : mu.card = (staircase m).card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
    have hfail : ∃ j, prefixSum (staircase m).rowLen j < prefixSum mu.rowLen j := by
      change ¬ ∀ j, prefixSum mu.rowLen j ≤ prefixSum (staircase m).rowLen j at hd
      push_neg at hd
      exact hd
    obtain ⟨j,hj⟩ := hfail
    have hjm : j < m := staircase_failed_prefix_range m mu hsize hj
    have hm : 1 ≤ m := by omega
    by_cases hl : m ≤ mu.rowLen 0
    · obtain ⟨h,he⟩ := Nat.exists_eq_add_of_le hm
      have he' : m = h+1 := by omega
      clear he
      subst m
      have hcore : ∀ p : Nat.Partition (staircase h).card,
          ∃ f : Representation.IntertwiningMap (spechtRep (partitionTableau p))
            (cyclicSubrepresentation (wordRep _ _) (staircaseWord h)).toRepresentation,
            Function.Injective f := by
        intro p
        exact ih h (by omega) (partitionDiagram p) (partitionTableau p)
      exact staircase_longRow_support h t hl hcore
    · have hrow : mu.rowLen 0 < m := by omega
      have hf : j*(2*m-j+1) < 2*prefixSum mu.rowLen j := by
        rw [← staircase_prefix_twice m hjm.le]
        omega
      have hdepth := short_row_failed_prefix_depth mu.rowLen_antitone hrow hjm.le hf
      have hm3 : 3 ≤ m := by omega
      obtain ⟨h,he⟩ := Nat.exists_eq_add_of_le (show 2 ≤ m by omega)
      have he' : m = h+2 := by omega
      clear he
      subst m
      have hh : 1 ≤ h := by omega
      have hnd : ¬ ∀ k, prefixSum mu.rowLen k ≤ prefixSum (staircase (h+2)).rowLen k := by
        intro H
        exact (Nat.not_le_of_lt hj) (H j)
      have hcore : ∀ p : Nat.Partition (staircase h).card,
          ∃ f : Representation.IntertwiningMap (spechtRep (partitionTableau p))
            (cyclicSubrepresentation (wordRep _ _) (staircaseWord h)).toRepresentation,
            Function.Injective f := by
        intro p
        exact ih h (by omega) (partitionDiagram p) (partitionTableau p)
      exact staircase_short_row_nondominated_support h hh t hrow hnd hcore

/-- The canonical smaller-core interface used by the one-step and two-step maps,
discharged with injections. -/
theorem staircase_canonical_core_support (m : ℕ)
    (p : Nat.Partition (staircase m).card) :
    ∃ f : Representation.IntertwiningMap (spechtRep (partitionTableau p))
      (cyclicSubrepresentation (wordRep _ _) (staircaseWord m)).toRepresentation,
      Function.Injective f :=
  staircase_universal_embedding m (partitionDiagram p) (partitionTableau p)

end HSTZ
#print axioms HSTZ.staircase_universal_embedding
#print axioms HSTZ.staircase_canonical_core_support
