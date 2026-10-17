import HSTZ.BalanceNeighboringPositions
import HSTZ.LetterLift

/-! Neighboring-component support, adapting `Support/Neighboring` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0), at the positions of `witnessAttachment`.
Existing tensor, letter, path and coordinate support proofs are reused. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def balanceNeighborLetter (r : ℕ) :
    Fin ((witnessAttachment r 1).transpose.transpose.colLen 0) → Fin 2 :=
  fun i => ⟨i.val,lt_of_lt_of_le i.isLt (by
    rw [YoungDiagram.transpose_transpose]
    exact witnessAttachment_rows r 1)⟩

theorem balanceNeighbor_left_word (r : ℕ) :
    letterLift (balanceNeighborLetter r)
      (polytabloid (transposeTableau (balanceNeighborTableau r)))=PathLayer.rowAlt r := by
  rw [polytabloid_eq_altWord,letterLift_altWord]
  have hg : columnGroup (transposeTableau (balanceNeighborTableau r))=
      columnGroup (balanceNeighborLayer r) := rfl
  rw [hg,balanceNeighborLayer_group]
  congr 1

theorem balanceNeighbor_move (r : ℕ) :
    tableauMove (transposeTableau (balanceNeighborTableau r))
      (transposeTableau (balanceNeighborRight r))=Fin.revPerm := by
  apply Equiv.ext
  intro i
  apply (transposeTableau (balanceNeighborRight r)).injective
  rw [tableauMove_apply]
  apply Subtype.ext
  change (balanceNeighborLayer r i).val=(balanceNeighborLayer r i.rev.rev).val
  rw [Fin.rev_rev]

theorem balanceNeighbor_right_word (r : ℕ) :
    letterLift (balanceNeighborLetter r)
      (polytabloid (transposeTableau (balanceNeighborRight r)))=
        wordRep (2*r+1) 2 Fin.revPerm (PathLayer.rowAlt r) := by
  rw [polytabloid_move (transposeTableau (balanceNeighborTableau r)),balanceNeighbor_move]
  rw [Representation.IntertwiningMap.isIntertwining]
  rw [balanceNeighbor_left_word]

theorem balanceNeighbor_pair_word (r : ℕ) :
    encodedLetterLift (balanceNeighborLetter r) (balanceNeighborLetter r)
      (wordTensor _ _ _
        (polytabloid (transposeTableau (balanceNeighborTableau r)) ⊗ₜ[ℂ]
          polytabloid (transposeTableau (balanceNeighborRight r))))=pathPairWord r := by
  rw [encodedLetterLift_tensor,balanceNeighbor_left_word,balanceNeighbor_right_word]
  rfl

private theorem balanceNeighbor_pair_support (r : ℕ) (hr : 2≤r) {nu : YoungDiagram}
    (v : Tableau (2*r+1) nu) (hnu : nu.colLen 0≤4) :
    ∃ f : Representation.IntertwiningMap (spechtRep v)
      (cyclic (wordRep (2*r+1)
        ((witnessAttachment r 1).transpose.transpose.colLen 0 *
          (witnessAttachment r 1).transpose.transpose.colLen 0))
        (wordTensor _ _ _
          (polytabloid (transposeTableau (balanceNeighborTableau r)) ⊗ₜ[ℂ]
            polytabloid (transposeTableau (balanceNeighborRight r))))).toRepresentation,
      Function.Injective f := by
  letI : NeZero (Nat.card (Equiv.Perm (Fin (2*r+1))) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card (Equiv.Perm (Fin (2*r+1)))).ne'⟩
  let D := encodedLetterLift (n := 2*r+1) (balanceNeighborLetter r) (balanceNeighborLetter r)
  let w := wordTensor _ _ _
    (polytabloid (transposeTableau (balanceNeighborTableau r)) ⊗ₜ[ℂ]
      polytabloid (transposeTableau (balanceNeighborRight r)))
  have hw : D w=pathPairWord r := balanceNeighbor_pair_word r
  obtain ⟨f,hf⟩ := fourRow_pathPair_embedding r hr v hnu
  have he : cyclic (wordRep (2*r+1) 4) (pathPairWord r)=
      cyclicSubrepresentation (wordRep (2*r+1) 4) (D w) := by
    apply SetLike.ext
    intro x
    change x∈cyclicSpan (wordRep (2*r+1) 4) (pathPairWord r) ↔
      x∈cyclicSpan (wordRep (2*r+1) 4) (D w)
    rw [hw]
  let E := equalSubrepresentationMap _ _ he
  obtain ⟨j,hj,_⟩ := cyclicImage_embedding_lift D w (E.comp f)
    ((equalSubrepresentationMap_bijective _ _ he).1.comp hf)
  have he' : cyclicSubrepresentation (wordRep (2*r+1) _) w=
      cyclic (wordRep (2*r+1) _) w := by
    apply SetLike.ext
    intro x
    rfl
  let E' := equalSubrepresentationMap _ _ he'
  exact ⟨E'.comp j,(equalSubrepresentationMap_bijective _ _ he').1.comp hj⟩

/-- All geometry, interval-survival and pair-cyclic inputs are discharged.
The codomain is the projected full square, not a repeated-vector cyclic module. -/
theorem balanceNeighbor_projected_support (r : ℕ) (hr : 2≤r)
    (t : Tableau (2*r+1) (witnessAttachment r 1).transpose) {nu : YoungDiagram}
    (v : Tableau (2*r+1) nu) (hnu : nu.colLen 0≤4) :
    ∃ J : Representation.IntertwiningMap (spechtRep v)
      (balanceProjectedSquare t (balanceInOutputs (Set.Icc r (r+1)))
        (balanceInOutputs_invariant (Set.Icc r (r+1)))).toRepresentation,
      Function.Injective J := by
  obtain ⟨f,hf⟩ := balanceNeighbor_pair_support r hr v hnu
  exact balanceProjected_support_of_pair t (balanceNeighborTableau r)
    (balanceNeighborRight r) v (balanceInOutputs (Set.Icc r (r+1)))
    (balanceInOutputs_invariant _) (balanceNeighbor_outputs r) f hf

end
end HSTZ
#print axioms HSTZ.balanceNeighborLetter
#print axioms HSTZ.balanceNeighbor_left_word
#print axioms HSTZ.balanceNeighbor_move
#print axioms HSTZ.balanceNeighbor_right_word
#print axioms HSTZ.balanceNeighbor_pair_word
#print axioms HSTZ.balanceNeighbor_projected_support
