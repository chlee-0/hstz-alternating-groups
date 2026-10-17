import HSTZ.WitnessBalancePackingBlockFamily

/-! Local support of every tower block in its joint/rest factor (part 2 of 3;
see `WitnessBalancePackingSupport`). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

private theorem degree_parts_joint :
    (witnessBalancePackingParts hk z .joint).length=2 := balancedPack_length (by norm_num)

/-- Local support of one tower block in its joint/rest factor, pulled back along
the block fiber relabelling. -/
theorem witnessBalance_block_local_support (hd : delta≤1)
    (hjoint : ∀ {nu : YoungDiagram} (t : Tableau (witnessBalancePackingJointDegree hk z) nu),
      nu.colLen 0≤2 → ∃ J : Representation.IntertwiningMap (spechtRep t) (witnessBalanceJointRep hk z),
        Function.Injective J)
    (v : TowerIdx (witnessBalancePackingBlocks k delta).length (witnessBalancePackingBlocks k delta).length)
    (q : Nat.Partition (witnessBalancePackingSelectedDegree hk z v.val))
    (hq : (partitionDiagram q).colLen 0≤(witnessBalancePackingParts hk z
      (witnessBalancePackingBlocks k delta)[v.val.val]).length) :
    ∃ L : Representation.IntertwiningMap (spechtRep (partitionTableau q))
      ((witnessBalanceBlockRep hk z (witnessBalancePackingBlockBeta k delta v)).comp
        (positionPermHom (witnessBalancePackingBlockFiber hk z hd v))), Function.Injective L := by
  suffices H : ∀ (x : Unit ⊕ witnessBalancePackingRestIndex k delta)
      (hx : witnessBalancePackingBlockTarget k delta v.val=x)
      (E : Fin (witnessBalancePackingSelectedDegree hk z v.val) ≃ Fin (witnessBalanceBlockSize hk z x)),
      ∃ L : Representation.IntertwiningMap (spechtRep (partitionTableau q))
        ((witnessBalanceBlockRep hk z x).comp (positionPermHom E)), Function.Injective L from
    H _ rfl (witnessBalancePackingBlockFiber hk z hd v)
  intro x hx E
  have hcardE : witnessBalancePackingSelectedDegree hk z v.val=witnessBalanceBlockSize hk z x := by
    simpa using Fintype.card_congr E
  apply specht_transport_injective E (witnessBalanceBlockRep hk z x) (partitionTableau q)
  unfold witnessBalancePackingBlockTarget at hx
  have hmem : (witnessBalancePackingBlocks k delta)[v.val.val]∈witnessBalancePackingBlocks k delta :=
    List.getElem_mem ..
  rcases x with ⟨⟩ | ⟨⟨a,ha⟩,hr⟩
  · have hj : (witnessBalancePackingBlocks k delta)[v.val.val]=.joint := by
      by_contra h
      rw [dif_neg h] at hx
      exact Sum.inr_ne_inl hx
    have h2 : (partitionDiagram q).colLen 0≤2 := by
      rw [hj,degree_parts_joint] at hq
      exact hq
    intro t'
    exact hjoint t' h2
  · have hj : (witnessBalancePackingBlocks k delta)[v.val.val]≠.joint := by
      intro h
      rw [dif_pos h] at hx
      exact Sum.inl_ne_inr hx
    rw [dif_neg hj] at hx
    have ha' : a=witnessBalancePackingBlockLabel (witnessBalancePackingBlocks k delta)[v.val.val] :=
      (congrArg (fun y : Unit ⊕ witnessBalancePackingRestIndex k delta =>
        Sum.elim (fun _ => 0) (fun r : witnessBalancePackingRestIndex k delta => r.val.val) y) hx).symm
    clear hx
    generalize (witnessBalancePackingBlocks k delta)[v.val.val]=q0 at hq hj ha' hmem
    subst ha'
    cases q0 with
    | joint => exact absurd rfl hj
    | tail =>
      have h1 : (partitionDiagram q).colLen 0≤1 := by
        simpa [witnessBalancePackingParts] using hq
      refine specht_shape_transfer _ ((eq_oneRowDiagram_of_colLen h1).trans
        (congrArg oneRowDiagram ((partitionDiagram_card q).trans hcardE))) ?_
      intro t'
      exact witnessBalance_tail_actual_tableau_support hk z t'
    | early s =>
      have hle : 3+delta≤k-2*s := by
        rcases (witnessBalance_packing_blocks_mem k delta _).mp hmem with h | ⟨_,h⟩ | ⟨s',h,hs'⟩
        · cases h
        · cases h
        · cases h
          exact hs'
      by_cases hu : k-2*s=3+delta
      · have h1 : (partitionDiagram q).colLen 0≤1 := by
          simpa [witnessBalancePackingParts,hu] using hq
        have hs : k-(2+delta)=2*s+1 := by omega
        refine specht_shape_transfer _ ((eq_oneRowDiagram_of_colLen h1).trans
          (congrArg oneRowDiagram ((partitionDiagram_card q).trans (hcardE.trans
            (witnessBalance_unmatched_positions_card hk z s hd hs))))) ?_
        intro t'
        exact witnessBalance_unmatched_actual_tableau_support hk z s hd hs t'
      · have h4 : (partitionDiagram q).colLen 0≤4 := by
          have hl : (witnessBalancePackingParts hk z (.early s)).length=4 := by
            simp only [witnessBalancePackingParts,if_neg hu]
            exact balancedPack_length (by norm_num)
          rw [hl] at hq
          exact hq
        have hs : 2*s+1<k-(2+delta) := by omega
        intro t'
        exact witnessBalance_neighbor_actual_tableau_support hk z s hs t' h4
end
end
end HSTZ
#print axioms HSTZ.witnessBalance_block_local_support
