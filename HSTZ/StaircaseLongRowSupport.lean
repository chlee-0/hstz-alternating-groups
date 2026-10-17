import HSTZ.StaircaseOnePieri
import HSTZ.StaircaseRightStrip
import HSTZ.ComplementSpecht

/-! One-step long-row support for the staircase. The results are conditional:
universality of the smaller staircase core (every canonical Specht module embeds)
is an explicit hypothesis `hcore`. The strip and the auxiliary data are constructed
in the proof. -/
namespace HSTZ
open OAI.Saxl

/-- The Specht classification transports the assumed canonical support to any core
tableau. -/
theorem staircase_core_embedding_of_canonical (h : ℕ) {nu : YoungDiagram}
    (s : Tableau (staircase h).card nu)
    (hcore : ∀ p : Nat.Partition (staircase h).card,
      ∃ f : Representation.IntertwiningMap (spechtRep (partitionTableau p))
        (cyclicSubrepresentation (wordRep _ _) (staircaseWord h)).toRepresentation,
        Function.Injective f) :
    ∃ f : Representation.IntertwiningMap (spechtRep s)
      (cyclicSubrepresentation (wordRep _ _) (staircaseWord h)).toRepresentation,
      Function.Injective f := by
  letI := specht_irreducible s
  obtain ⟨p, J, hJ⟩ := irreducible_specht_intertwiner (spechtRep s)
  obtain ⟨f, hf⟩ := hcore p
  exact ⟨f.comp J, hf.comp hJ.1⟩

/-- Assuming `hcore`, a target whose first row has length at least `h+1` embeds,
by removing a strip of size `h+1`. -/
theorem staircase_longRow_support (h : ℕ) {mu : YoungDiagram}
    (t : Tableau (staircase (h+1)).card mu) (hm : h+1 ≤ mu.rowLen 0)
    (hcore : ∀ p : Nat.Partition (staircase h).card,
      ∃ f : Representation.IntertwiningMap (spechtRep (partitionTableau p))
        (cyclicSubrepresentation (wordRep _ _) (staircaseWord h)).toRepresentation,
        Function.Injective f) :
    ∃ E : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic (h+1)).toRepresentation, Function.Injective E := by
  obtain ⟨nu, s, hs, _⟩ := exists_staircase_rightStrip (h+1) t hm
  have s' : Tableau (staircase h).card nu := by
    simpa only [Nat.add_sub_cancel] using s
  obtain ⟨f, hf⟩ := staircase_core_embedding_of_canonical h s' hcore
  exact staircase_oneStep_strip_support h s' t hs f hf

end HSTZ
#print axioms HSTZ.staircase_core_embedding_of_canonical
#print axioms HSTZ.staircase_longRow_support
