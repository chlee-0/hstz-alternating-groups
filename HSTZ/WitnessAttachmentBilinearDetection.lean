import HSTZ.IntertwiningCompat
import HSTZ.WitnessAttachmentColumnParitySupport

/-! Bilinear detection of the selected attachment generator, keeping position
translates. Reuses the `cyclic_star`, `wordPair_move` and Specht detection APIs,
building on OpenAI's `math` repository (commit adc7f1241, Apache-2.0). This gives an intertwiner
pairing, not a tensor-power `wordMap` matrix or a common flag. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem attachment_alt_real {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) :
    star (altWord G a) = altWord G a := by
  classical
  unfold altWord
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [star_smul,wordRep_star]
  simp only [signC_def,star_intCast]
  congr 2
  ext w
  simp [Pi.single_apply]

theorem witnessSelectedAttachmentPairWord_real (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    star (witnessSelectedAttachmentPairWord k b delta hp) =
      witnessSelectedAttachmentPairWord k b delta hp := by
  have hr : star (witnessSelectedAttachmentRowWord k b delta hp) =
      witnessSelectedAttachmentRowWord k b delta hp := attachment_alt_real _ _
  have hc : star (witnessSelectedAttachmentColumnWord k b delta hp) =
      witnessSelectedAttachmentColumnWord k b delta hp := attachment_alt_real _ _
  funext w
  change star (witnessSelectedAttachmentPairWord k b delta hp w) = _
  unfold witnessSelectedAttachmentPairWord
  rw [wordTensor_tmul,star_mul]
  change star (witnessSelectedAttachmentColumnWord k b delta hp (splitRight w)) *
    star (witnessSelectedAttachmentRowWord k b delta hp (splitLeft w)) = _
  have hcv := congrFun hc (splitRight w)
  have hrv := congrFun hr (splitLeft w)
  change star (witnessSelectedAttachmentColumnWord k b delta hp (splitRight w)) = _ at hcv
  change star (witnessSelectedAttachmentRowWord k b delta hp (splitLeft w)) = _ at hrv
  rw [hcv,hrv]
  exact mul_comm _ _

private theorem attachment_cyclic_pair_detect {n d : ℕ}
    (u : WordSpace n d) (hu : star u = u) {x : WordSpace n d}
    (hx : x ∈ cyclic (wordRep n d) u) (hx0 : x ≠ 0) :
    ∃ g : Equiv.Perm (Fin n), dotProduct (wordRep n d g x) u ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hy : ∀ y ∈ (cyclic (wordRep n d) u).toSubmodule,
      dotProduct x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g,rfl⟩ := hy
      have he := wordPair_move g⁻¹ x u
      rw [inv_inv] at he
      exact he.symm.trans (h g⁻¹)
    | zero => exact dotProduct_zero _
    | add y z hy hz ihy ihz => rw [dotProduct_add,ihy,ihz,add_zero]
    | smul c y hy ih => rw [dotProduct_smul,ih,smul_zero]
  have hs := cyclic_star u hu hx
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact hx0 (dotProduct_self_star_eq_zero.mp (hy (star x) hs))

/-- Some position translate pairs nontrivially through a Specht injection.
The map is not asserted to be `wordMap L`. -/
theorem witnessSelectedAttachment_intertwiner_translate_pair (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b delta).card mu)
    (hc : ColumnParity mu.colLen delta) (ht : mu.rowLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
        (witnessAttachmentCyclic k b delta hp).toRepresentation,
      Function.Injective F.toLinearMap ∧
      ∃ sigma : Equiv.Perm (Fin (witnessAttachment b delta).card),
        dotProduct (F (spechtRep t sigma.symm
          ⟨polytabloid t,mem_cyclic _ _⟩)).val
          (witnessSelectedAttachmentPairWord k b delta hp) ≠ 0 := by
  obtain ⟨F,hF⟩ := witnessSelectedAttachment_parity_embedding k b delta hp t hc ht
  let p : Specht t := ⟨polytabloid t,mem_cyclic _ _⟩
  have hp0 : p ≠ 0 := by
    intro hz
    exact polytabloid_ne_zero t (congrArg Subtype.val hz)
  have hx0 : (F p).val ≠ 0 := by
    intro hz
    have hf : F p = 0 := Subtype.ext hz
    exact hp0 (hF (hf.trans (map_zero F.toLinearMap).symm))
  have hx : (F p).val ∈ cyclic (wordRep _ _)
      (witnessSelectedAttachmentPairWord k b delta hp) := (F p).property
  obtain ⟨g,hg⟩ := attachment_cyclic_pair_detect _
    (witnessSelectedAttachmentPairWord_real k b delta hp) hx hx0
  refine ⟨F,hF,g.symm,?_⟩
  have he := F.map_action g p
  have hv := congrArg Subtype.val he
  change (F (spechtRep t g p)).val = wordRep _ _ g (F p).val at hv
  simpa only [Equiv.symm_symm] using (hv ▸ hg)

/-- An ambient intertwiner detects some position translate of the polytabloid.
This map is not shown to lie in the span of tensor-power `wordMap`s. -/
theorem witnessSelectedAttachment_ambient_translate_pair (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b delta).card mu)
    (hc : ColumnParity mu.colLen delta) (ht : mu.rowLen 0 ≤ 4) :
    ∃ G : Representation.IntertwiningMap
        (wordRep (witnessAttachment b delta).card (mu.colLen 0))
        (wordRep (witnessAttachment b delta).card
          ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
            (witnessDiagram k b delta hp.staircase_bound).colLen 0)),
      ∃ sigma : Equiv.Perm (Fin (witnessAttachment b delta).card),
        dotProduct (G (wordRep _ _ sigma.symm (polytabloid t)))
          (witnessSelectedAttachmentPairWord k b delta hp) ≠ 0 := by
  obtain ⟨F,hF,sigma,hpair⟩ :=
    witnessSelectedAttachment_intertwiner_translate_pair k b delta hp t hc ht
  let pr := subrepProject (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
  let inc : Representation.IntertwiningMap
      (witnessAttachmentCyclic k b delta hp).toRepresentation (wordRep _ _) :=
    { toLinearMap := (witnessAttachmentCyclic k b delta hp).toSubmodule.subtype
      isIntertwining' := fun g => LinearMap.ext <| fun x => rfl }
  let G := inc.comp (F.comp pr)
  let x : Specht t := spechtRep t sigma.symm ⟨polytabloid t,mem_cyclic _ _⟩
  have hproj : pr x.val = x := subrepProject_subtype (spechtSub t) _ x
  refine ⟨G,sigma,?_⟩
  change dotProduct (F (pr x.val)).val
    (witnessSelectedAttachmentPairWord k b delta hp) ≠ 0
  rw [hproj]
  exact hpair

/-- The full complement source is real, by the alternant calculation; rows may
cross between path and attachment before selection. -/
theorem witnessComplementPairWord_real (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hk)) :
    star (witnessComplementPairWord k b delta hk z)=
      witnessComplementPairWord k b delta hk z := by
  have hr : star (witnessComplementRowWord k b delta hk z)=
      witnessComplementRowWord k b delta hk z := attachment_alt_real _ _
  have hc : star (witnessComplementColumnWord k b delta hk z)=
      witnessComplementColumnWord k b delta hk z := attachment_alt_real _ _
  funext w
  change star (witnessComplementPairWord k b delta hk z w)=_
  unfold witnessComplementPairWord
  rw [wordTensor_tmul,star_mul]
  have hcv := congrFun hc (splitRight w)
  have hrv := congrFun hr (splitLeft w)
  change star (witnessComplementColumnWord k b delta hk z (splitRight w))=_ at hcv
  change star (witnessComplementRowWord k b delta hk z (splitLeft w))=_ at hrv
  change star (witnessComplementColumnWord k b delta hk z (splitRight w)) *
    star (witnessComplementRowWord k b delta hk z (splitLeft w))=_
  rw [hcv,hrv]
  exact mul_comm _ _

end
end HSTZ
#print axioms HSTZ.witnessSelectedAttachmentPairWord_real
#print axioms HSTZ.witnessSelectedAttachment_intertwiner_translate_pair

#print axioms HSTZ.witnessSelectedAttachment_ambient_translate_pair

#print axioms HSTZ.witnessComplementPairWord_real
