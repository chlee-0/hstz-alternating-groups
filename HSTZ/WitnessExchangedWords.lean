import HSTZ.WitnessExchangedCoordinates
import HSTZ.WitnessPathBases

/-! The explicitly exchanged path row word and the signed pair over the full
complement. Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This uses a changed base; it does not establish the identity for the original
binary base. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessLowRowLetter (k b delta : ℕ) (hk : 5 ≤ k) :
    Fin 2 ↪ Fin ((witnessDiagram k b delta hk).transpose.colLen 0) where
  toFun i := ⟨i.val,by
    rw [YoungDiagram.colLen_transpose,witnessDiagram_width]
    have hi := i.isLt
    omega⟩
  inj' := by
    intro i j he
    have hv := congrArg (fun a : Fin ((witnessDiagram k b delta hk).transpose.colLen 0) => a.val) he
    exact Fin.ext (show i.val=j.val from hv)

theorem witnessExchangedRowBase_path (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta) :
    (fun i : Fin (witnessPathSize k) => witnessExchangedRowBase k b delta hk hr
      (witnessComplementOrder k b delta (.inl i)))=
      fun i => witnessLowRowLetter k b delta hk (PathLayer.base i) := by
  funext i
  apply Fin.ext
  change (witnessExchangedRowBase k b delta hk hr
    (witnessComplementOrder k b delta (.inl i))).val=(PathLayer.base i).val
  have hb : (PathLayer.base i).val=if i.val=0 then 0 else (i.val+1)%2 := by
    unfold PathLayer.base
    split_ifs <;> rfl
  rw [witnessExchangedRowBase_all,hb]
  have hno : witnessComplementOrder k b delta (.inl i)≠witnessComplementOrigin k b delta hr := by
    intro he
    have hh := (witnessComplementOrder k b delta).injective he
    cases hh
  by_cases hi : i=witnessPathEndpoint k
  · subst i
    rw [if_pos (show witnessComplementOrder k b delta (.inl (witnessPathEndpoint k))=
      witnessComplementEndpoint k b delta from rfl)]
    have hn : (witnessPathEndpoint k).val≠0 := by
      change 2*((k-2)+1)≠0
      omega
    rw [if_neg hn]
    change 1=(2*((k-2)+1)+1)%2
    omega
  · have hne : witnessComplementOrder k b delta (.inl i)≠witnessComplementEndpoint k b delta := by
      intro he
      exact hi (Sum.inl.inj ((witnessComplementOrder k b delta).injective he))
    rw [if_neg hne,if_neg hno,witnessComplementRowBase_path]
    exact witnessPathRowBase_nonendpoint k b delta hk i hi

theorem witness_exchanged_row_alternant (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk)) :
    altWord (witnessComplementRowGroup k b delta hk) (witnessExchangedRowBase k b delta hk hr)=
      -witnessComplementRowWord k b delta hk t := by
  have he := witness_complement_row_covariance k b delta hk t
    (witnessEndpointExchange k b delta hk hr)
  change altWord (witnessComplementRowGroup k b delta hk) (witnessExchangedRowBase k b delta hk hr)=
    signC (witnessEndpointExchangePerm k b delta hr) • witnessComplementRowWord k b delta hk t at he
  rw [witnessEndpointExchange_sign,neg_one_smul] at he
  exact he

def witnessExchangedComplementPairWord (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta) :
    WordSpace (witnessComplementSize k b delta)
      ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) :=
  wordTensor _ _ _ (altWord (witnessComplementRowGroup k b delta hk)
    (witnessExchangedRowBase k b delta hk hr) ⊗ₜ[ℂ]
      altWord (witnessComplementColumnGroup k b delta hk) (witnessComplementColumnBase k b delta hk))

theorem witness_exchanged_pair (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessExchangedComplementPairWord k b delta hk hr= -witnessComplementPairWord k b delta hk t := by
  unfold witnessExchangedComplementPairWord
  rw [witness_exchanged_row_alternant k b delta hk hr t,
    ← witness_complement_column_alternant k b delta hk t]
  rw [TensorProduct.neg_tmul,map_neg]
  rfl

theorem witnessExchangedComplementPairWord_ne_zero (k b delta : ℕ) (hk : 5 ≤ k) (hr : 0<b+delta) :
    witnessExchangedComplementPairWord k b delta hk hr≠0 := by
  rw [witness_exchanged_pair k b delta hk hr (witnessTableau k b delta hk)]
  exact neg_ne_zero.mpr (witnessComplementPairWord_ne_zero k b delta hk (witnessTableau k b delta hk))

end
end HSTZ
#print axioms HSTZ.witnessLowRowLetter
#print axioms HSTZ.witnessExchangedRowBase_path
#print axioms HSTZ.witness_exchanged_row_alternant
#print axioms HSTZ.witness_exchanged_pair
#print axioms HSTZ.witnessExchangedComplementPairWord_ne_zero
