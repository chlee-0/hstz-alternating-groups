import HSTZ.WitnessAttachmentEvenNoncancellation
import HSTZ.BalanceOutputTwoTensor

/-! Symmetric even-row support in the output-two filtered square.
Adapts `Balance/BalancedPairs` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0) to the witness
attachment geometry, using noncancellation of the contraction with H. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

theorem balanceOutputTwo_even_embedding (m : ℕ) {nu : YoungDiagram}
    (v : Tableau (witnessAttachment m 0).card nu) (he : AttachmentEvenRows nu)
    (ht : nu.colLen 0≤2) :
    ∃ F : Representation.IntertwiningMap (spechtRep v)
      (cyclic (wordRep (witnessAttachment m 0).card 2)
        (balanceOutputTwoOrdered m)).toRepresentation, Function.Injective F := by
  let L := balanceOutputTwoTargetLetters v ht
  let x : (spechtSub v).toSubmodule :=
    ⟨wordRep _ _ (attachmentTargetEvenMatching v he).symm (polytabloid v),
      (spechtSub v).apply_mem_toSubmodule _ (mem_cyclic _ _)⟩
  have hnz : dotProduct (wordMap L x.val) (balanceOutputTwoOrdered m)≠0 := by
    rw [balanceOutputTwo_target_pair v ht m x.val]
    change dotProduct (wordMap _ (wordRep _ _ (attachmentTargetEvenMatching v he).symm
      (polytabloid v))) (attachmentHTensor m 0)≠0
    rw [attachmentTargetEvenAlternant_original,attachmentTargetEvenContraction_full_sum]
    exact attachmentTargetEvenColumnSum_ne_zero v he (ht.trans (by omega : 2≤4)) 0
  obtain ⟨F,hF⟩ := hom_to_cyclic_of_pair L (spechtSub v) x
    (balanceOutputTwoOrdered m) (balanceOutputTwoOrdered_real m) hnz
  change Representation.IntertwiningMap (spechtRep v)
    (cyclic (wordRep _ 2) (balanceOutputTwoOrdered m)).toRepresentation at F
  letI := specht_irreducible v
  exact ⟨F,(Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

theorem balanceOutputTwo_height (m : ℕ) (hm : 1 ≤ m) :
    2≤(witnessAttachment m 0).colLen 0 := by
  have hc : (1,0)∈witnessAttachment m 0 :=
    (mem_witnessAttachment m 0 1 0).mpr (.inr ⟨rfl,by omega⟩)
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hc
  omega

def balanceOutputTwoActualLetter (m : ℕ) (hm : 1 ≤ m) (i : Fin 2) :
    Fin ((witnessAttachment m 0).colLen 0*(witnessAttachment m 0).colLen 0) :=
  finProdFinEquiv (Fin.castLE (balanceOutputTwo_height m hm) i,
    Fin.castLE (balanceOutputTwo_height m hm) i.rev)

theorem balanceOutputTwoActualLetter_output (m : ℕ) (hm : 1 ≤ m) (i : Fin 2) :
    balancePairOutput (balanceOutputTwoActualLetter m hm i)=2 := by
  simp only [balancePairOutput,balanceOutputTwoActualLetter,Equiv.symm_apply_apply,
    Fin.val_castLE,Fin.val_rev]
  have hi := i.isLt
  omega

def balanceOutputTwoTableau (m : ℕ) :
    Tableau (witnessAttachment m 0).card (witnessAttachment m 0) :=
  (witnessAttachmentColumnEnumeration m 0).trans (witnessCanonicalAttachment m 0)

theorem balanceOutputTwoTableau_polytabloid (m : ℕ) :
    letterLift (witnessAttachmentBinaryLetter m 0) (polytabloid (balanceOutputTwoTableau m))=
      attachmentOrderedColumnAlt m 0 := by
  rw [polytabloid_eq_altWord,letterLift_altWord]
  change altWord (fiberGroup (fun i => (witnessCanonicalAttachment m 0
    (witnessAttachmentColumnEnumeration m 0 i)).val.2))
      ((witnessAttachmentBinaryLetter m 0 ∘ rowWord (witnessCanonicalAttachment m 0)) ∘
        witnessAttachmentColumnEnumeration m 0)=_
  rw [witnessAttachmentOrderedColumnFiber,witnessAttachmentOrderedBinaryBase_exact]
  rfl

private theorem balanceOutputTwoTableau_eval (m : ℕ)
    (w : Fin (witnessAttachment m 0).card → Fin ((witnessAttachment m 0).colLen 0)) :
    polytabloid (balanceOutputTwoTableau m) w=
      attachmentOrderedColumnAlt m 0 (witnessAttachmentBinaryLetter m 0 ∘ w) := by
  have he := congrFun (balanceOutputTwoTableau_polytabloid m)
    (witnessAttachmentBinaryLetter m 0 ∘ w)
  rw [letterLift_eval _ (witnessAttachmentBinaryLetter m 0).injective] at he
  exact he

theorem balanceOutputTwo_squared_polytabloid (m : ℕ) (hm : 1 ≤ m)
    (w : Fin (witnessAttachment m 0).card → Fin 2) :
    wordTensor _ _ _ (polytabloid (balanceOutputTwoTableau m) ⊗ₜ[ℂ]
      polytabloid (balanceOutputTwoTableau m)) (balanceOutputTwoActualLetter m hm ∘ w)=
        (-1:ℂ)^m*balanceOutputTwoOrdered m w := by
  rw [wordTensor_tmul,balanceOutputTwoTableau_eval,balanceOutputTwoTableau_eval]
  have hl : witnessAttachmentBinaryLetter m 0 ∘
      splitLeft (balanceOutputTwoActualLetter m hm ∘ w)=w := by
    funext i
    apply Fin.ext
    simp [splitLeft,balanceOutputTwoActualLetter,witnessAttachmentBinaryLetter]
    rfl
  have hr : witnessAttachmentBinaryLetter m 0 ∘
      splitRight (balanceOutputTwoActualLetter m hm ∘ w)=Fin.rev ∘ w := by
    funext i
    apply Fin.ext
    simp [splitRight,balanceOutputTwoActualLetter,witnessAttachmentBinaryLetter]
    change 2 - ((w i).val + 1) = 1 - (w i).val
    omega
  rw [hl,hr]
  have he := congrFun (attachmentOrderedRepeatedWord_HPower m 0) (balanceOutputTwoLetter ∘ w)
  change attachmentOrderedRepeatedWord m 0 (balanceOutputTwoLetter ∘ w)=
    attachmentHTensor m 0 (balanceOutputTwoLetter ∘ w) at he
  rw [balanceOutputTwoHTensor] at he
  rw [← he]
  rw [attachmentOrderedRepeatedWord,wordTensor_tmul]
  have hleft : splitLeft (d := 2) (e := 2) (balanceOutputTwoLetter ∘ w)=w := by
    funext i
    simp [splitLeft,balanceOutputTwoLetter]
  have hright : splitRight (d := 2) (e := 2) (balanceOutputTwoLetter ∘ w)=Fin.rev ∘ w := by
    funext i
    simp [splitRight,balanceOutputTwoLetter]
  rw [hleft,hright]

/-- Every even-row target with at most two rows occurs in the output-two
filtered square. The selector, source coordinates and nonzero maps are constructed
in the proof. -/
theorem balanceOutputTwo_projected_support (m : ℕ) (hm : 1 ≤ m)
    (t : Tableau (witnessAttachment m 0).card (witnessAttachment m 0)) {nu : YoungDiagram}
    (v : Tableau (witnessAttachment m 0).card nu) (he : AttachmentEvenRows nu)
    (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep v)
      (balanceProjectedSquare t (balanceInOutputs ({2} : Set ℕ))
        (balanceInOutputs_invariant ({2} : Set ℕ))).toRepresentation, Function.Injective J := by
  classical
  let P := balanceInOutputs (n := (witnessAttachment m 0).card)
    (d := (witnessAttachment m 0).colLen 0) (e := (witnessAttachment m 0).colLen 0) ({2} : Set ℕ)
  let hP := balanceInOutputs_invariant (n := (witnessAttachment m 0).card)
    (d := (witnessAttachment m 0).colLen 0) (e := (witnessAttachment m 0).colLen 0) ({2} : Set ℕ)
  let W := balanceProjectedSquare t P hP
  let p : Specht t := ⟨polytabloid (balanceOutputTwoTableau m),
    polytabloid_mem_all t (balanceOutputTwoTableau m)⟩
  let y := coordinateProjection P (wordTensor _ _ _ (p.val ⊗ₜ[ℂ] p.val))
  have hy : y∈W.toSubmodule := by
    exact ⟨p ⊗ₜ[ℂ] p,rfl⟩
  let z : W.toSubmodule := ⟨y,hy⟩
  let D : Representation.IntertwiningMap W.toRepresentation
      (wordRep (witnessAttachment m 0).card 2) :=
    { toLinearMap :=
        { toFun := fun x w => x.val (balanceOutputTwoActualLetter m hm ∘ w)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => LinearMap.ext (fun _ => rfl) }
  have hz : D z=(-1:ℂ)^m • balanceOutputTwoOrdered m := by
    funext w
    change coordinateProjection P (wordTensor _ _ _
      (polytabloid (balanceOutputTwoTableau m) ⊗ₜ[ℂ] polytabloid (balanceOutputTwoTableau m)))
        (balanceOutputTwoActualLetter m hm ∘ w)=_
    rw [coordinateProjection_apply,if_pos]
    · exact balanceOutputTwo_squared_polytabloid m hm w
    · intro i
      exact balanceOutputTwoActualLetter_output m hm (w i)
  obtain ⟨f,hf⟩ := balanceOutputTwo_even_embedding m v he ht
  letI : NeZero (Nat.card (Equiv.Perm (Fin (witnessAttachment m 0).card)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card (Equiv.Perm (Fin (witnessAttachment m 0).card))).ne'⟩
  have hc : cyclic (wordRep _ 2) (balanceOutputTwoOrdered m)=
      cyclicSubrepresentation (wordRep _ 2) (D z) := by
    apply SetLike.ext
    intro x
    change x∈cyclicSpan (wordRep _ 2) (balanceOutputTwoOrdered m) ↔
      x∈cyclicSpan (wordRep _ 2) (D z)
    rw [hz,cyclicSpan_smul_nonzero _ _ (pow_ne_zero m (by norm_num))]
  let E := equalSubrepresentationMap _ _ hc
  obtain ⟨j,hj,_⟩ := cyclicImage_embedding_lift D z (E.comp f)
    ((equalSubrepresentationMap_bijective _ _ hc).1.comp hf)
  let inc : Representation.IntertwiningMap
      (cyclicSubrepresentation W.toRepresentation z).toRepresentation W.toRepresentation :=
    { toLinearMap := Submodule.subtype _
      isIntertwining' := fun _ => LinearMap.ext (fun _ => rfl) }
  have hi : Function.Injective inc := fun _ _ hh => Subtype.ext hh
  exact ⟨inc.comp j,hi.comp hj⟩

end
end HSTZ
#print axioms HSTZ.balanceOutputTwo_even_embedding
#print axioms HSTZ.balanceOutputTwoActualLetter_output
#print axioms HSTZ.balanceOutputTwoTableau_polytabloid
#print axioms HSTZ.balanceOutputTwo_squared_polytabloid
#print axioms HSTZ.balanceOutputTwo_projected_support
