import HSTZ.WitnessPathWords
import HSTZ.WitnessTableau
import OAI.RepresentationTheory.Saxl.PathAlternation

/-! Asymmetric path letters.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0); the arithmetic
proofs here are new. The endpoint is kept rather than replaced by a native binary letter. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem witnessPath_nonendpoint_half (k : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) (hi : i≠witnessPathEndpoint k) :
    i.val/2≠k-1 := by
  have hb := i.isLt
  change i.val<2*((k-2)+1)+1 at hb
  have hn : i.val≠2*((k-2)+1) := by
    intro he
    apply hi
    exact Fin.ext he
  omega

theorem witnessPathRowBase_nonendpoint (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) (hi : i≠witnessPathEndpoint k) :
    (witnessPathRowBase k b delta hk i).val=
      if i.val=0 then 0 else (i.val+1)%2 := by
  rw [witnessPathRowBase_value,if_neg (witnessPath_nonendpoint_half k hk i hi)]
  have hb := i.isLt
  change i.val<2*((k-2)+1)+1 at hb
  have hn := witnessPath_nonendpoint_half k hk i hi
  unfold witnessRowForward witnessRowTailForward witnessFirstRowForward
  split_ifs <;> omega

theorem witnessPathColumnBase_nonendpoint (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) (hi : i≠witnessPathEndpoint k) :
    (witnessPathColumnBase k b delta hk i).val=(i.val+1)%2 := by
  rw [witnessPathColumnBase_value,if_neg (witnessPath_nonendpoint_half k hk i hi)]
  have hb := i.isLt
  change i.val<2*((k-2)+1)+1 at hb
  have hn := witnessPath_nonendpoint_half k hk i hi
  split_ifs <;> omega

theorem witnessPathRowBase_all (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) :
    (witnessPathRowBase k b delta hk i).val=
      if i=witnessPathEndpoint k then witnessFirstRowForward k b (k+b+delta-1)
      else if i.val=0 then 0 else (i.val+1)%2 := by
  classical
  by_cases hi : i=witnessPathEndpoint k
  · subst i
    simpa using witnessPathRowBase_endpoint k b delta hk
  · simpa only [hi,if_false] using witnessPathRowBase_nonendpoint k b delta hk i hi

theorem witnessPathColumnBase_all (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) :
    (witnessPathColumnBase k b delta hk i).val=
      if i=witnessPathEndpoint k then 0 else (i.val+1)%2 := by
  classical
  by_cases hi : i=witnessPathEndpoint k
  · subst i
    simpa using witnessPathColumnBase_endpoint k b delta hk
  · simpa only [hi,if_false] using witnessPathColumnBase_nonendpoint k b delta hk i hi

theorem witnessPathRowBase_endpoint_empty (k : ℕ) (hk : 5 ≤ k) :
    (witnessPathRowBase k 0 0 hk (witnessPathEndpoint k)).val=1 := by
  rw [witnessPathRowBase_endpoint]
  unfold witnessFirstRowForward
  split_ifs <;> omega

theorem witnessPathRowBase_endpoint_even (k b : ℕ) (hk : 5 ≤ k) (hb : 1≤b) :
    (witnessPathRowBase k b 0 hk (witnessPathEndpoint k)).val=k+b-2 := by
  rw [witnessPathRowBase_endpoint]
  unfold witnessFirstRowForward
  split_ifs <;> omega

theorem witnessPathRowBase_endpoint_odd (k b : ℕ) (hk : 5 ≤ k) :
    (witnessPathRowBase k b 1 hk (witnessPathEndpoint k)).val=k+b := by
  rw [witnessPathRowBase_endpoint]
  unfold witnessFirstRowForward
  split_ifs <;> omega

theorem witnessPathRowBase_endpoint_paper (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    2≤(witnessPathRowBase k b delta hp.staircase_bound (witnessPathEndpoint k)).val := by
  have hk := hp.staircase_bound
  have hd := hp.parity
  have hr := hp.positive_remainder
  have hcases : delta=0 ∨ delta=1 := by omega
  rcases hcases with rfl | rfl
  · rw [witnessPathRowBase_endpoint_even k b hk (by omega)]
    omega
  · rw [witnessPathRowBase_endpoint_odd]
    omega

end
end HSTZ
#print axioms HSTZ.witnessPath_nonendpoint_half
#print axioms HSTZ.witnessPathRowBase_nonendpoint
#print axioms HSTZ.witnessPathColumnBase_nonendpoint
#print axioms HSTZ.witnessPathRowBase_all
#print axioms HSTZ.witnessPathColumnBase_all
#print axioms HSTZ.witnessPathRowBase_endpoint_empty
#print axioms HSTZ.witnessPathRowBase_endpoint_even
#print axioms HSTZ.witnessPathRowBase_endpoint_odd
#print axioms HSTZ.witnessPathRowBase_endpoint_paper
