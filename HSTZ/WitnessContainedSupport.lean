import HSTZ.YoungDiagramCompat
import HSTZ.WitnessBlockInduction
import HSTZ.BlockInductionSwap
import HSTZ.ContainedSpechtSupport

/-! The chosen contained theta, the other core partition and the original target
Specht module. Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Order transport is the native block/tensor bijection, not a swap of sources. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

abbrev witnessComplementFirstInduced (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hk)) {mu theta : YoungDiagram}
    (u : Tableau (staircase (k-2)).card mu)
    (s : Tableau (witnessComplementSize k b delta) theta) := by
  letI : AddCommGroup (Specht s ⊗[ℂ] Specht u) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht s ⊗[ℂ] Specht u) := TensorProduct.leftModule
  exact Representation.ind (sumPermHom (swapPositionBlocks (witnessBinaryCut k b delta hk z)))
    (independentTensor (spechtRep s) (spechtRep u))

/-- The existing native transport, fully typed, including its ambient generator equation. -/
private def witnessInductionSwap (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hk)) {mu theta : YoungDiagram}
    (u : Tableau (staircase (k-2)).card mu)
    (s : Tableau (witnessComplementSize k b delta) theta) :=
  @exists_blockInductionSwap ℂ (Specht u) (Specht s)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    n (staircase (k-2)).card (witnessComplementSize k b delta)
    (witnessBinaryCut k b delta hk z) (spechtRep u) (spechtRep s)

theorem containedWitness_complement_first_embedding
    {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c ≤ h c)
    (hclear : t*d+4 ≤ witnessPathSize k)
    (hcapacity : witnessPathSize k ≤ prefixSum (capacity h d) m)
    (hsize : prefixSum e m = 2*b+delta) (hzero : ∀ c, t ≤ c → e c = 0)
    (mu : YoungDiagram) (u : Tableau (staircase (k-2)).card mu)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (hpi : (containedPath h hh d (witnessPathSize k) m).colLen 0 ≤ 4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0 ≤ 4) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap
      (witnessComplementFirstInduced k b delta hp.staircase_bound z u s)
      (cyclic (wordRep n ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
        (witnessMixedWord k b delta hp.staircase_bound z)).toRepresentation,
      Function.Injective F := by
  obtain ⟨M,hM,_⟩ := witnessInductionSwap k b delta hp.staircase_bound z u s
  obtain ⟨N,hN⟩ := containedWitness_block_induced_embedding hh he k b delta hp
    htm hroom hclear hcapacity hsize hzero mu u s hpi hc hE z
  exact ⟨N.comp M,hN.comp hM.1⟩

/-- Theta is the first contained factor; classification chooses the other core
partition. The original target tableau and ambient positions remain unchanged. -/
theorem containedWitness_target_embedding
    {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c ≤ h c)
    (hclear : t*d+4 ≤ witnessPathSize k)
    (hcapacity : witnessPathSize k ≤ prefixSum (capacity h d) m)
    (hsize : prefixSum e m = 2*b+delta) (hzero : ∀ c, t ≤ c → e c = 0)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (hpi : (containedPath h hh d (witnessPathSize k) m).colLen 0 ≤ 4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0 ≤ 4) {n : ℕ} {nu : YoungDiagram}
    (target : Tableau n nu)
    (hcont : containedWhole h e hh he d (witnessPathSize k) m ≤ nu)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap (spechtRep target)
      (cyclic (wordRep n ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
        (witnessMixedWord k b delta hp.staircase_bound z)).toRepresentation,
      Function.Injective F := by
  obtain ⟨p,J,hJ⟩ := contained_specht_embedding_of_containment s target hcont
    (swapPositionBlocks (witnessBinaryCut k b delta hp.staircase_bound z))
  obtain ⟨N,hN⟩ := containedWitness_complement_first_embedding hh he k b delta hp
    htm hroom hclear hcapacity hsize hzero _ (partitionTableau p) s hpi hc hE z
  exact ⟨N.comp J,hN.comp hJ⟩

/-- The greedy theta lies in the original target, with no chosen sector as input. -/
theorem containedWitness_theta_le (nu : YoungDiagram) {e : ℕ → ℕ}
    (he : Antitone e) {d K m t : ℕ}
    (hroom : ∀ c < t, d+e c ≤ nu.colLen c)
    (hzero : ∀ c, t ≤ c → e c = 0) (hclear : t*d+4 ≤ K) :
    containedWhole nu.colLen e nu.colLen_antitone he d K m ≤ nu := by
  intro x hx
  obtain ⟨_,hr⟩ := (mem_fromColumns _ _ _ _ _).mp hx
  apply YoungDiagram.mem_iff_lt_colLen.mpr
  exact hr.trans_le (attached_le_height hroom hzero (by omega) x.2)

/-- Capacity and clearance give target containment, for the original target and
witness data and the same contained theta tableau. -/
theorem containedWitness_target_capacity_embedding
    {e : ℕ → ℕ} (he : Antitone e) {d m t : ℕ}
    (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) {n : ℕ} {nu : YoungDiagram}
    (target : Tableau n nu) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c ≤ nu.colLen c)
    (hclear : t*d+4 ≤ witnessPathSize k)
    (hcapacity : witnessPathSize k ≤ prefixSum (capacity nu.colLen d) m)
    (hsize : prefixSum e m = 2*b+delta) (hzero : ∀ c, t ≤ c → e c = 0)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole nu.colLen e nu.colLen_antitone he d (witnessPathSize k) m))
    (hpi : (containedPath nu.colLen nu.colLen_antitone d (witnessPathSize k) m).colLen 0 ≤ 4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0 ≤ 4)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap (spechtRep target)
      (cyclic (wordRep n ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
        (witnessMixedWord k b delta hp.staircase_bound z)).toRepresentation,
      Function.Injective F :=
  containedWitness_target_embedding nu.colLen_antitone he k b delta hp htm hroom hclear
    hcapacity hsize hzero s hpi hc hE target
    (containedWitness_theta_le nu he hroom hzero hclear) z
/-- The cardinality of theta is determined by the original capacity data. -/
theorem containedWitness_theta_card {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m : ℕ} (k b delta : ℕ)
    (hcapacity : witnessPathSize k ≤ prefixSum (capacity h d) m)
    (hsize : prefixSum e m = 2*b+delta) :
    (containedWhole h e hh he d (witnessPathSize k) m).card =
      witnessComplementSize k b delta := by
  rw [fromColumns_card,prefix_attached h e d (witnessPathSize k) m hcapacity,hsize]
  change witnessPathSize k + (2*b+delta) =
    witnessPathSize k + (witnessAttachment b delta).card
  rw [witnessAttachment_card]

/-- The canonical theta tableau is chosen internally from its cardinality equality.
No arbitrary contained tableau or matching witness is supplied. -/
theorem containedWitness_target_capacity_canonical_embedding
    {e : ℕ → ℕ} (he : Antitone e) {d m t : ℕ}
    (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) {n : ℕ} {nu : YoungDiagram}
    (target : Tableau n nu) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c ≤ nu.colLen c)
    (hclear : t*d+4 ≤ witnessPathSize k)
    (hcapacity : witnessPathSize k ≤ prefixSum (capacity nu.colLen d) m)
    (hsize : prefixSum e m = 2*b+delta) (hzero : ∀ c, t ≤ c → e c = 0)
    (hpi : (containedPath nu.colLen nu.colLen_antitone d (witnessPathSize k) m).colLen 0 ≤ 4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0 ≤ 4)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap (spechtRep target)
      (cyclic (wordRep n ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
        (witnessMixedWord k b delta hp.staircase_bound z)).toRepresentation,
      Function.Injective F := by
  let s := canonicalTableau (containedWhole nu.colLen e nu.colLen_antitone he d (witnessPathSize k) m)
    (containedWitness_theta_card nu.colLen_antitone he k b delta hcapacity hsize)
  exact containedWitness_target_capacity_embedding he k b delta hp target htm hroom
    hclear hcapacity hsize hzero s hpi hc hE z

end
end HSTZ
#print axioms HSTZ.containedWitness_complement_first_embedding
#print axioms HSTZ.containedWitness_target_embedding
#print axioms HSTZ.containedWitness_theta_le
#print axioms HSTZ.containedWitness_target_capacity_embedding

#print axioms HSTZ.containedWitness_theta_card
#print axioms HSTZ.containedWitness_target_capacity_canonical_embedding
