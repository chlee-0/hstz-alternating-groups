import HSTZ.WitnessLowSector

/-! Coefficients after the selected complement projection.
Adapts the coefficient-one strategy of `polytabloid_rowWord` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0) to rotated cell coordinates. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

theorem witnessComplementCell_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessComplementCell k b delta hk) := by
  intro i j he
  let t := witnessTableau k b delta hk
  have ht : t ((witnessBinaryCut k b delta hk t).symm (.inr i))=
      t ((witnessBinaryCut k b delta hk t).symm (.inr j)) := by
    simpa only [witnessComplementCell_original] using he
  exact Sum.inr.inj ((witnessBinaryCut k b delta hk t).symm.injective (t.injective ht))

theorem witnessExchangedRow_stabilizer (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta)
    (g : witnessComplementRowGroup k b delta hk)
    (hg : witnessExchangedRowBase k b delta hk hr ∘ (g : Equiv.Perm _) =
      witnessExchangedRowBase k b delta hk hr) : g=1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply (witnessEndpointExchangePerm k b delta hr).injective
  apply witnessComplementCell_injective k b delta hk
  apply (witnessRowRotation k b delta hk).injective
  apply Subtype.ext
  apply Prod.ext
  · have hs := (witnessEndpointExchange k b delta hk hr).property
    have hrow := g.property i
    change (witnessComplementCell k b delta hk
      (witnessEndpointExchangePerm k b delta hr ((g : Equiv.Perm (Fin (witnessComplementSize k b delta))) i))).val.1=
      (witnessComplementCell k b delta hk
        (witnessEndpointExchangePerm k b delta hr i)).val.1
    exact (hs ((g : Equiv.Perm (Fin (witnessComplementSize k b delta))) i)).trans (hrow.trans (hs i).symm)
  · exact congrArg Fin.val (congrFun hg i)

theorem witnessComplementColumn_stabilizer (k b delta : ℕ) (hk : 5 ≤ k)
    (g : witnessComplementColumnGroup k b delta hk)
    (hg : witnessComplementColumnBase k b delta hk ∘ (g : Equiv.Perm _) =
      witnessComplementColumnBase k b delta hk) : g=1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply witnessComplementCell_injective k b delta hk
  apply (witnessColumnRotation k b delta hk).injective
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Fin.val (congrFun hg i)
  · simpa only [witnessColumnRotation_column, OneMemClass.coe_one,
      Equiv.Perm.one_apply] using g.property i

theorem witnessSelectedRowWord_coefficient (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    witnessSelectedRowWord k b delta hp
      (witnessExchangedRowBase k b delta hp.staircase_bound
        (paperWitness_attachment_positive k b delta hp))=1 := by
  classical
  unfold witnessSelectedRowWord altWord
  simp only [Finset.sum_apply,Pi.smul_apply,wordRep,MonoidHom.coe_mk,
    OneHom.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,Pi.single_apply]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro g hg hg1
    have hn : witnessExchangedRowBase k b delta hp.staircase_bound
        (paperWitness_attachment_positive k b delta hp) ∘ (g : Equiv.Perm _) ≠
        witnessExchangedRowBase k b delta hp.staircase_bound
          (paperWitness_attachment_positive k b delta hp) := by
      intro he
      have hh := witnessExchangedRow_stabilizer k b delta hp.staircase_bound
        (paperWitness_attachment_positive k b delta hp) ⟨g.val,g.property.1⟩ he
      apply hg1
      apply Subtype.ext
      exact congrArg (fun h : witnessComplementRowGroup k b delta hp.staircase_bound =>
        (h : Equiv.Perm (Fin (witnessComplementSize k b delta)))) hh
    simp [hn]
  · simp

theorem witnessComplementColumnWord_coefficient (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessComplementColumnWord k b delta hk t (witnessComplementColumnBase k b delta hk)=1 := by
  classical
  rw [witness_complement_column_alternant]
  unfold altWord
  simp only [Finset.sum_apply,Pi.smul_apply,wordRep,MonoidHom.coe_mk,
    OneHom.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,Pi.single_apply]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro g hg hg1
    have hn : witnessComplementColumnBase k b delta hk ∘ (g : Equiv.Perm _)≠
        witnessComplementColumnBase k b delta hk :=
      fun h => hg1 (witnessComplementColumn_stabilizer k b delta hk g h)
    simp [hn]
  · simp

def witnessSelectedComplementPairWord (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    WordSpace (witnessComplementSize k b delta)
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
       (witnessDiagram k b delta hp.staircase_bound).colLen 0) :=
  wordTensor _ _ _ (witnessSelectedRowWord k b delta hp ⊗ₜ[ℂ]
    altWord (witnessComplementColumnGroup k b delta hp.staircase_bound)
      (witnessComplementColumnBase k b delta hp.staircase_bound))

theorem witnessSelectedComplementPairWord_coefficient (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    witnessSelectedComplementPairWord k b delta hp
      (mergeWords (witnessExchangedRowBase k b delta hp.staircase_bound
        (paperWitness_attachment_positive k b delta hp))
        (witnessComplementColumnBase k b delta hp.staircase_bound))=1 := by
  unfold witnessSelectedComplementPairWord
  rw [wordTensor_tmul,splitLeft_merge,splitRight_merge,witnessSelectedRowWord_coefficient]
  rw [← witness_complement_column_alternant k b delta hp.staircase_bound
    (witnessTableau k b delta hp.staircase_bound),witnessComplementColumnWord_coefficient,one_mul]

theorem witnessSelectedComplementPairWord_ne_zero (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) : witnessSelectedComplementPairWord k b delta hp≠0 := by
  intro hz
  have he := witnessSelectedComplementPairWord_coefficient k b delta hp
  rw [hz] at he
  exact zero_ne_one he

end
end HSTZ
#print axioms HSTZ.witnessComplementCell_injective
#print axioms HSTZ.witnessExchangedRow_stabilizer
#print axioms HSTZ.witnessComplementColumn_stabilizer
#print axioms HSTZ.witnessSelectedRowWord_coefficient
#print axioms HSTZ.witnessComplementColumnWord_coefficient
#print axioms HSTZ.witnessSelectedComplementPairWord_coefficient
#print axioms HSTZ.witnessSelectedComplementPairWord_ne_zero
