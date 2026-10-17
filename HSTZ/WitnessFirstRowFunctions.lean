import HSTZ.WitnessMarkedLetters

/-! The first-row relabelling functions of the witness and their inverse
identities, for every `k ≥ 5`, including an empty attachment. Uses witness
declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ

def witnessFirstRowForward (k b c : ℕ) : ℕ :=
  if c<k-3 then c+2
  else if c=k-3 then k+b-1
  else if c<k then c-(k-2)
  else if c<k+b then c-1
  else c

def witnessFirstRowBackward (k b a : ℕ) : ℕ :=
  if a<2 then a+k-2
  else if a<k-1 then a-2
  else if a=k+b-1 then k-3
  else if a<k+b-1 then a+1
  else a

theorem witnessFirstRowBackward_forward (k b delta c : ℕ) (hk : 5 ≤ k)
    (_hc : c<k+b+delta) :
    witnessFirstRowBackward k b (witnessFirstRowForward k b c)=c := by
  unfold witnessFirstRowForward
  split_ifs <;> unfold witnessFirstRowBackward <;> split_ifs <;> omega

theorem witnessFirstRowForward_backward (k b delta a : ℕ) (hk : 5 ≤ k)
    (_ha : a<k+b+delta) :
    witnessFirstRowForward k b (witnessFirstRowBackward k b a)=a := by
  unfold witnessFirstRowBackward
  split_ifs <;> unfold witnessFirstRowForward <;> split_ifs <;> omega

end HSTZ
#print axioms HSTZ.witnessFirstRowBackward_forward
#print axioms HSTZ.witnessFirstRowForward_backward
