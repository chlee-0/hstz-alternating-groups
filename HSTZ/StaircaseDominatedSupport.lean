import OAI.RepresentationTheory.Saxl.DominatedSupport

import OAI.RepresentationTheory.Saxl.CyclicTensor

import OAI.RepresentationTheory.Saxl.DominatedQuotient

import HSTZ.SpechtSignTransport
import HSTZ.PieriSupport
import HSTZ.ProjectionLift

/-! Dominated support for the native staircase cyclic space, without a sign
twist: every Specht module whose shape `mu` satisfies `Dominates (staircase m) mu`
embeds in it.
Follows the `DominatedSupport` composition in OpenAI's `math` repository
(commit adc7f1241, Apache-2.0), with the map, inverse and surjective-lift steps
ported to the older API. -/
namespace HSTZ
open OAI.Saxl

/-- A surjective intertwiner from the native staircase cyclic space onto the
Specht module, obtained from the dominated quotient and the two sign transports.
Every `m`, including zero, is allowed. -/
theorem staircase_dominated_surjection (m : ℕ) (mu : YoungDiagram)
    (t : Tableau (staircase m).card mu) (hmu : Dominates (staircase m) mu) :
    ∃ R : Representation.IntertwiningMap (staircaseCyclic m).toRepresentation
      (spechtRep t), Function.Surjective R := by
  classical
  have hc : mu.card = (staircase m).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have ht : mu.transpose.card = (staircase m).card := by rw [transpose_card, hc]
  have hd : Dominates mu.transpose (staircase m) := by
    simpa only [staircase_transpose] using dominates_transpose hc.symm hmu
  have hw (j : Fin ((staircase m).colLen 0)) :
      (Finset.univ.filter (fun i => repeatedTarget m i = Fin.rev j)).card =
        (staircase m).rowLen j := by
    simpa only [repeatedTarget, Fin.rev_inj] using rowWord_content (stairTableau m) j
  obtain ⟨F,hF⟩ := young_orbit_map (staircase m) mu.transpose (transposeTableau t)
    ht hd (repeatedTarget m) Fin.revPerm hw
  obtain ⟨phi⟩ := staircase_sign_equiv m
  let Q : Representation.IntertwiningMap (signTwist (staircaseCyclic m).toRepresentation)
      (spechtRep (transposeTableau t)) := F.comp (dominatedQuotient m phi)
  have hQ : Q ≠ 0 := by
    obtain ⟨x,hx⟩ := repeatedTarget_in_quotient m phi
    intro hz
    apply hF
    have hh := congrArg (fun L : Representation.IntertwiningMap
      (signTwist (staircaseCyclic m).toRepresentation) (spechtRep (transposeTableau t)) => L x) hz
    change F (dominatedQuotient m phi x) = 0 at hh
    change dominatedQuotient m phi x =
      Pi.single (M := fun _ => ℂ) (repeatedTarget m) (1:ℂ) at hx
    rw [hx] at hh
    exact hh
  let R : Representation.IntertwiningMap (staircaseCyclic m).toRepresentation (spechtRep t) :=
    (spechtSignInverseMap t).comp (signCancelMap Q)
  have hR : R ≠ 0 := by
    intro hz
    apply hQ
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun L : Representation.IntertwiningMap
      (staircaseCyclic m).toRepresentation (spechtRep t) => L x) hz
    change (spechtSignEquiv t).symm (Q x) = 0 at hx
    exact (spechtSignEquiv t).symm.injective
      (hx.trans (map_zero (spechtSignEquiv t).symm.toLinearMap).symm)
  letI := specht_irreducible t
  exact ⟨R, intertwiner_surjective_of_irreducible R hR⟩

/-- The surjection splits: there is an equivariant embedding `E` with
`R (E x) = x`. -/
theorem staircase_dominated_split_embedding (m : ℕ) (mu : YoungDiagram)
    (t : Tableau (staircase m).card mu) (hmu : Dominates (staircase m) mu) :
    ∃ (R : Representation.IntertwiningMap (staircaseCyclic m).toRepresentation (spechtRep t))
      (E : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic m).toRepresentation),
      Function.Surjective R ∧ Function.Injective E ∧ ∀ x, R (E x) = x := by
  obtain ⟨R,hR⟩ := staircase_dominated_surjection m mu t hmu
  letI : NeZero (Nat.card (Equiv.Perm (Fin (staircase m).card)) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_pos.ne')⟩
  obtain ⟨E,hE,hcomp⟩ := equivariant_injective_lift R hR
    (Representation.IntertwiningMap.id (spechtRep t)) Function.injective_id
  exact ⟨R,E,hR,hE,hcomp⟩

/-- The target Specht module embeds into the native staircase cyclic space,
including degree zero. Dominance is the usual prefix-sum condition. -/
theorem staircase_dominated_embedding (m : ℕ) (mu : YoungDiagram)
    (t : Tableau (staircase m).card mu) (hmu : Dominates (staircase m) mu) :
    ∃ E : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic m).toRepresentation, Function.Injective E := by
  obtain ⟨R,E,hR,hE,hcomp⟩ := staircase_dominated_split_embedding m mu t hmu
  exact ⟨E,hE⟩

end HSTZ
#print axioms HSTZ.staircase_dominated_surjection
#print axioms HSTZ.staircase_dominated_split_embedding
#print axioms HSTZ.staircase_dominated_embedding
