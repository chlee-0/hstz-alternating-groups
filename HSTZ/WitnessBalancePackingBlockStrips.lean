import HSTZ.WitnessBalancePackingOrderedStrips

/-! Coherent strip boundaries for the physical packing blocks: one sequence of
Young diagrams groups the ordered strips by block. The list splitting is done by
private lemmas. The choice of compatible local Specht modules is handled
separately. Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical

private theorem chain_split {full : List ℕ} {nu mu : YoungDiagram}
    (hs : SizedStripChain full nu mu) :
    ∀ a b : List ℕ, full=a++b →
      ∃ eta, SizedStripChain a nu eta ∧ SizedStripChain b eta mu := by
  induction hs with
  | nil nu =>
    intro a b he
    obtain ⟨ha,hb⟩ := List.append_eq_nil_iff.mp he.symm
    subst a
    subst b
    exact ⟨nu,SizedStripChain.nil nu,SizedStripChain.nil nu⟩
  | @snoc cs nu eta mu c hs hh hc ih =>
    intro a b he
    rcases List.eq_nil_or_concat' b with hb | ⟨bs,d,rfl⟩
    · subst b
      simp only [List.append_nil] at he
      exact ⟨mu,he ▸ SizedStripChain.snoc hs hh hc,SizedStripChain.nil mu⟩
    · have he' : cs++[c]=(a++bs)++[d] := by simpa only [List.append_assoc] using he
      have hlen : cs.length=(a++bs).length := by
        have ht := congrArg List.length he'
        simp only [List.length_append,List.length_singleton] at ht
        simp only [List.length_append]
        omega
      obtain ⟨hp,hl⟩ := List.append_inj he' hlen
      have hd : c=d := by simpa using hl
      subst d
      obtain ⟨eta',ha,hb⟩ := ih a bs hp
      exact ⟨eta',ha,SizedStripChain.snoc hb hh hc⟩

private theorem chain_card {bs : List ℕ} {nu mu : YoungDiagram}
    (hs : SizedStripChain bs nu mu) : nu.card+bs.sum=mu.card := by
  induction hs with
  | nil => simp
  | snoc hs hh hc ih =>
    simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
    omega

private theorem chain_empty {bs : List ℕ} {nu mu : YoungDiagram}
    (hs : SizedStripChain bs nu mu) (he : bs=[]) : nu=mu := by
  cases hs with
  | nil => rfl
  | snoc hs hh hc => simp at he

private theorem group_chain (qs : List WitnessBalancePackingKind)
    (parts : WitnessBalancePackingKind → List ℕ) {nu mu : YoungDiagram}
    (hs : SizedStripChain (qs.flatMap parts) nu mu) :
    ∃ D : Fin (qs.length+1) → YoungDiagram,
      D 0=nu ∧ D (Fin.last qs.length)=mu ∧
      ∀ j : Fin qs.length, SizedStripChain (parts qs[j.val])
        (D j.castSucc) (D j.succ) := by
  induction qs generalizing nu with
  | nil =>
    simp only [List.flatMap_nil] at hs
    have hm := chain_empty hs rfl
    subst mu
    exact ⟨fun _ => nu,rfl,rfl,fun j => Fin.elim0 j⟩
  | cons q qs ih =>
    simp only [List.flatMap_cons] at hs
    obtain ⟨eta,hfirst,hrest⟩ := chain_split hs (parts q) (qs.flatMap parts) rfl
    obtain ⟨D,hzero,hlast,hsteps⟩ := ih hrest
    let E : Fin ((q::qs).length+1) → YoungDiagram := Fin.cons nu D
    refine ⟨E,by simp [E],?_,?_⟩
    · change E (Fin.succ (Fin.last qs.length))=mu
      simpa [E] using hlast
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa [E,hzero] using hfirst
      · simpa [E] using hsteps i

section Actual
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

/-- The parts of each block sum to the block degree, including blocks of degree
zero. -/
theorem witnessBalance_packing_parts_sum (q : WitnessBalancePackingKind) :
    (witnessBalancePackingParts hk z q).sum=witnessBalancePackingDegree hk z q := by
  cases q with
  | joint => exact balancedPack_sum (by decide : 0<2)
  | tail => simp [witnessBalancePackingParts]
  | early s =>
    simp only [witnessBalancePackingParts]
    split_ifs
    · simp
    · exact balancedPack_sum (by decide : 0<4)

/-- The number of strips in each block. This counts parts; it is not a bound on
the height of a local representation. -/
theorem witnessBalance_packing_parts_length (q : WitnessBalancePackingKind) :
    (witnessBalancePackingParts hk z q).length=
      match q with
      | .joint => 2
      | .tail => 1
      | .early s => if k-2*s=3+delta then 1 else 4 := by
  cases q with
  | joint => exact balancedPack_length (by decide : 0<2)
  | tail => simp [witnessBalancePackingParts]
  | early s =>
    simp only [witnessBalancePackingParts]
    split_ifs
    · rfl
    · exact balancedPack_length (by decide : 0<4)
end Actual

/-- A single sequence of diagrams groups the ordered strips by physical packing
block. Each increment is the number of positions in the corresponding block. -/
theorem paperWitness_balance_physical_block_strips (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    ∃ D : Fin ((witnessBalancePackingBlocks k delta).length+1) → YoungDiagram,
      D 0=⊥ ∧ D (Fin.last (witnessBalancePackingBlocks k delta).length)=mu ∧
      ∀ j : Fin (witnessBalancePackingBlocks k delta).length,
        SizedStripChain
          (witnessBalancePackingParts hp.staircase_bound z (witnessBalancePackingBlocks k delta)[j.val])
          (D j.castSucc) (D j.succ) ∧
        (D j.succ).card=(D j.castSucc).card+
          Fintype.card {i : Fin n // witnessBalancePackingPositionKind hp.staircase_bound z i=
            (witnessBalancePackingBlocks k delta)[j.val]} := by
  have hs : SizedStripChain ((witnessBalancePackingBlocks k delta).flatMap
      (witnessBalancePackingParts hp.staircase_bound z)) ⊥ mu := by
    rw [witnessBalance_packing_blocks_flatten hp.staircase_bound z hp.parity]
    exact paperWitness_balance_ordered_stripChain k b delta hp z s hprefix
  obtain ⟨D,hzero,hlast,hsteps⟩ := group_chain _ _ hs
  refine ⟨D,hzero,hlast,?_⟩
  intro j
  refine ⟨hsteps j,?_⟩
  have hc := chain_card (hsteps j)
  rw [witnessBalance_packing_parts_sum hp.staircase_bound z,
    witnessBalance_packing_block_card hp.staircase_bound z hp.parity _
      (List.getElem_mem j.isLt)] at hc
  exact hc.symm
private theorem horizontal_height {nu mu : YoungDiagram} (hs : HorizontalStrip nu mu) :
    mu.colLen 0≤nu.colLen 0+1 := by
  by_contra h
  have hx : (nu.colLen 0,0)∈mu := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hy : (nu.colLen 0+1,0)∈mu := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hnx : (nu.colLen 0,0)∉nu := by
    intro hh
    have ht := YoungDiagram.mem_iff_lt_colLen.mp hh
    omega
  have hny : (nu.colLen 0+1,0)∉nu := by
    intro hh
    have ht := YoungDiagram.mem_iff_lt_colLen.mp hh
    omega
  have he := hs.2 _ hx hnx _ hy hny rfl
  have hf := congrArg Prod.fst he
  omega

private theorem chain_height {bs : List ℕ} {nu mu : YoungDiagram}
    (hs : SizedStripChain bs nu mu) : mu.colLen 0≤nu.colLen 0+bs.length := by
  induction hs with
  | nil => simp
  | snoc hs hh hc ih =>
    have ht := horizontal_height hh
    simp only [List.length_append,List.length_singleton]
    omega

/-- A two-row joint tableau of the joint degree is selected from the global ordered
strip chain; the remaining ordered block parts connect it to the target. -/
theorem paperWitness_balance_joint_strip_choice (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    ∃ (tau : YoungDiagram) (t : Tableau (witnessBalancePackingJointDegree hp.staircase_bound z) tau),
      tau.colLen 0≤2 ∧
      SizedStripChain (witnessBalancePackingParts hp.staircase_bound z .joint) ⊥ tau ∧
      SizedStripChain (((witnessBalancePackingBlocks k delta).drop 1).flatMap
        (witnessBalancePackingParts hp.staircase_bound z)) tau mu := by
  have hs : SizedStripChain ((witnessBalancePackingBlocks k delta).flatMap
      (witnessBalancePackingParts hp.staircase_bound z)) ⊥ mu := by
    rw [witnessBalance_packing_blocks_flatten hp.staircase_bound z hp.parity]
    exact paperWitness_balance_ordered_stripChain k b delta hp z s hprefix
  have hblocks : witnessBalancePackingBlocks k delta=
      .joint::(witnessBalancePackingBlocks k delta).drop 1 := by
    simp [witnessBalancePackingBlocks]
  rw [hblocks,List.flatMap_cons] at hs
  obtain ⟨tau,hjoint,hrest⟩ := chain_split hs _ _ rfl
  have hzero : (⊥ : YoungDiagram).colLen 0=0 := by
    apply Nat.eq_zero_of_not_pos
    intro hh
    have hm : (0,0)∈(⊥ : YoungDiagram) := YoungDiagram.mem_iff_lt_colLen.mpr hh
    simpa using hm
  have hheight := chain_height hjoint
  rw [hzero,witnessBalance_packing_parts_length hp.staircase_bound z .joint] at hheight
  have hrow : tau.colLen 0≤2 := by simpa using hheight
  have hdegree : witnessBalancePackingDegree hp.staircase_bound z .joint=
      witnessBalancePackingJointDegree hp.staircase_bound z := by
    simp [witnessBalancePackingDegree,witnessBalancePackingLabels,
      witnessBalancePackingJointDegree,witnessBalancePackingJointLabel]
  have hcard := chain_card hjoint
  rw [witnessBalance_packing_parts_sum hp.staircase_bound z,hdegree] at hcard
  have hbotcard : (⊥ : YoungDiagram).card=0 := by rfl
  have htcard : tau.card=witnessBalancePackingJointDegree hp.staircase_bound z := by
    simpa only [hbotcard,Nat.zero_add] using hcard.symm
  exact ⟨tau,canonicalTableau tau htcard,hrow,hjoint,hrest⟩

/-- For the selected two-row joint type there is a surjective, nonzero restriction
map from the target Specht module, with a coloring by the remaining parts and
covariance under compatible permutations. The color stabilizer is neither the
group H nor the full rest-product action. -/
theorem paperWitness_balance_selected_joint_restriction (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    ∃ (tau : YoungDiagram) (t : Tableau (witnessBalancePackingJointDegree hp.staircase_bound z) tau),
      tau.colLen 0≤2 ∧
    ∃ hs : SizedStripChain (((witnessBalancePackingBlocks k delta).drop 1).flatMap
        (witnessBalancePackingParts hp.staircase_bound z)) tau mu,
    ∃ (c : Fin n → ℕ) (F : Specht s →ₗ[ℂ] Specht t),
      Function.Surjective F ∧ F≠0 ∧
      (∀ i, c i≤(((witnessBalancePackingBlocks k delta).drop 1).flatMap
        (witnessBalancePackingParts hp.staircase_bound z)).length) ∧
      (∀ i, c i=0 ↔ i∈Set.range (tableauInclusion t s hs.le)) ∧
      (∀ j (hj : j<(((witnessBalancePackingBlocks k delta).drop 1).flatMap
          (witnessBalancePackingParts hp.staircase_bound z)).length),
        (Finset.univ.filter (fun i => c i=j+1)).card=
          (((witnessBalancePackingBlocks k delta).drop 1).flatMap
            (witnessBalancePackingParts hp.staircase_bound z))[j]) ∧
      (∀ (g : Equiv.Perm (Fin n))
          (h : Equiv.Perm (Fin (witnessBalancePackingJointDegree hp.staircase_bound z))),
        (∀ i, c (g i)=c i) →
        (∀ v, g (tableauInclusion t s hs.le v)=tableauInclusion t s hs.le (h v)) →
        ∀ x, F (spechtRep s g x)=spechtRep t h (F x)) := by
  classical
  obtain ⟨tau,t,hrow,hjoint,hs⟩ := paperWitness_balance_joint_strip_choice k b delta hp z s hprefix
  obtain ⟨c,F,hF,hc,hzero,hcount,he⟩ := stripChain_restriction_any hs t s
  let v : Specht t := ⟨polytabloid t,mem_cyclic _ _⟩
  have hv : v≠0 := by
    intro hh
    exact polytabloid_ne_zero t (congrArg Subtype.val hh)
  have hne : F≠0 := by
    intro hh
    obtain ⟨x,hx⟩ := hF v
    apply hv
    exact hx.symm.trans (by simpa using LinearMap.congr_fun hh x)
  exact ⟨tau,t,hrow,hs,c,F,hF,hne,hc,hzero,hcount,he⟩

end
end HSTZ
#print axioms HSTZ.witnessBalance_packing_parts_sum
#print axioms HSTZ.witnessBalance_packing_parts_length
#print axioms HSTZ.paperWitness_balance_physical_block_strips

#print axioms HSTZ.paperWitness_balance_joint_strip_choice

#print axioms HSTZ.paperWitness_balance_selected_joint_restriction
