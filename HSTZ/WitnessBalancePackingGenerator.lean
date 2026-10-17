import HSTZ.WitnessBalancePackingSquare

/-! Polytabloid coordinates over all original label fibers.
Reuses the one-cut factorization and `polytabloid_rowWord` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). Base coefficients are computed internally. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
  (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessBalancePackingRowTuple :=
  ∀ a : witnessBalancePackingLabelIndex k delta,
    Fin (witnessBalanceComponentSize hk z a.val) → Fin ((witnessDiagram k b delta hk).colLen 0)

def witnessBalancePackingBaseCoefficient (a : ℕ) : ℂ :=
  witnessBalanceComponentWord hk z a
    (leftWord (witnessBalanceComponentCut hk z a) (rowWord z))

theorem witnessBalancePackingBaseCoefficient_ne_zero (a : ℕ) :
    witnessBalancePackingBaseCoefficient hk z a ≠ 0 := by
  have h := congrFun (witnessBalance_component_polytabloid hk z a) (rowWord z)
  rw [polytabloid_rowWord] at h
  change 1=witnessBalancePackingBaseCoefficient hk z a *
    witnessBalanceOtherWord hk z a (rightWord (witnessBalanceComponentCut hk z a) (rowWord z)) at h
  intro hz
  rw [hz,zero_mul] at h
  exact one_ne_zero h

def witnessBalancePackingRowAssembly (hd : delta ≤ 1)
    (v : witnessBalancePackingRowTuple hk z) : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0) :=
  fun i => v (witnessBalancePackingLabelCut hk z hd i).1
    (witnessBalancePackingLabelCut hk z hd i).2

private def baseRows : witnessBalancePackingRowTuple hk z :=
  fun a => leftWord (witnessBalanceComponentCut hk z a.val) (rowWord z)

private theorem rowAssembly_left (hd : delta ≤ 1)
    (v : witnessBalancePackingRowTuple hk z) (a : witnessBalancePackingLabelIndex k delta) :
    leftWord (witnessBalanceComponentCut hk z a.val) (witnessBalancePackingRowAssembly hk z hd v)=v a := by
  let E := witnessBalancePackingLabelCut hk z hd
  funext j
  have hp : (witnessBalanceComponentCut hk z a.val).symm (.inl j)=E.symm ⟨a,j⟩ := rfl
  change v (E ((witnessBalanceComponentCut hk z a.val).symm (.inl j))).1
    (E ((witnessBalanceComponentCut hk z a.val).symm (.inl j))).2=v a j
  rw [hp]
  exact congrArg (fun t : Σ a : witnessBalancePackingLabelIndex k delta,
    Fin (witnessBalanceComponentSize hk z a.val) => v t.1 t.2) (E.apply_symm_apply ⟨a,j⟩)

private theorem rowAssembly_base (hd : delta ≤ 1) :
    witnessBalancePackingRowAssembly hk z hd (baseRows hk z)=rowWord z := by
  let E := witnessBalancePackingLabelCut hk z hd
  funext i
  change rowWord z (E.symm (E i))=rowWord z i
  exact congrArg (rowWord z) (E.symm_apply_apply i)

private def partialRows (s : Finset (witnessBalancePackingLabelIndex k delta))
    (v : witnessBalancePackingRowTuple hk z) : witnessBalancePackingRowTuple hk z :=
  fun a => if a∈s then v a else baseRows hk z a

private theorem partialRows_right_insert (hd : delta ≤ 1)
    (s : Finset (witnessBalancePackingLabelIndex k delta))
    (v : witnessBalancePackingRowTuple hk z) (a : witnessBalancePackingLabelIndex k delta) :
    rightWord (witnessBalanceComponentCut hk z a.val)
      (witnessBalancePackingRowAssembly hk z hd (partialRows hk z (insert a s) v))=
    rightWord (witnessBalanceComponentCut hk z a.val)
      (witnessBalancePackingRowAssembly hk z hd (partialRows hk z s v)) := by
  let E := witnessBalancePackingLabelCut hk z hd
  funext j
  let i := (witnessBalanceComponentCut hk z a.val).symm (.inr j)
  have hn : (E i).1 ≠ a := by
    intro h
    apply witnessBalanceComponentCut_right hk z a.val j
    exact (witnessBalancePackingLabelCut_label hk z hd i).symm.trans (congrArg Subtype.val h)
  change (if (E i).1∈insert a s then v (E i).1 else baseRows hk z (E i).1) (E i).2=
    (if (E i).1∈s then v (E i).1 else baseRows hk z (E i).1) (E i).2
  simp only [Finset.mem_insert,hn,false_or]

private theorem generator_partialRows (hd : delta ≤ 1)
    (v : witnessBalancePackingRowTuple hk z)
    (s : Finset (witnessBalancePackingLabelIndex k delta)) :
    polytabloid z (witnessBalancePackingRowAssembly hk z hd (partialRows hk z s v))=
      ∏ a∈s, witnessBalanceComponentWord hk z a.val (v a) /
        witnessBalancePackingBaseCoefficient hk z a.val := by
  induction s using Finset.induction_on with
  | empty =>
    have he : partialRows hk z ∅ v=baseRows hk z := by funext a; simp [partialRows]
    rw [he,rowAssembly_base,polytabloid_rowWord,Finset.prod_empty]
  | @insert a s ha ih =>
    let cut := witnessBalanceComponentCut hk z a.val
    let w := witnessBalancePackingRowAssembly hk z hd (partialRows hk z s v)
    let w' := witnessBalancePackingRowAssembly hk z hd (partialRows hk z (insert a s) v)
    have hl : leftWord cut w=baseRows hk z a := by
      rw [rowAssembly_left]
      simp only [partialRows,ha,if_false]
    have hl' : leftWord cut w'=v a := by
      rw [rowAssembly_left]
      simp only [partialRows,Finset.mem_insert_self,if_pos]
    have hr : rightWord cut w'=rightWord cut w := partialRows_right_insert hk z hd s v a
    have hs := congrFun (witnessBalance_component_polytabloid hk z a.val) w
    have hs' := congrFun (witnessBalance_component_polytabloid hk z a.val) w'
    change polytabloid z w=witnessBalanceComponentWord hk z a.val (leftWord cut w)*
      witnessBalanceOtherWord hk z a.val (rightWord cut w) at hs
    change polytabloid z w'=witnessBalanceComponentWord hk z a.val (leftWord cut w')*
      witnessBalanceOtherWord hk z a.val (rightWord cut w') at hs'
    rw [hl] at hs
    rw [hl',hr] at hs'
    rw [Finset.prod_insert ha,← ih]
    change polytabloid z w'=(witnessBalanceComponentWord hk z a.val (v a)/
      witnessBalancePackingBaseCoefficient hk z a.val)*polytabloid z w
    rw [hs,hs']
    change witnessBalanceComponentWord hk z a.val (v a)*witnessBalanceOtherWord hk z a.val (rightWord cut w)=
      (witnessBalanceComponentWord hk z a.val (v a)/witnessBalancePackingBaseCoefficient hk z a.val)*
        (witnessBalancePackingBaseCoefficient hk z a.val*witnessBalanceOtherWord hk z a.val (rightWord cut w))
    field_simp [witnessBalancePackingBaseCoefficient_ne_zero hk z a.val]

/-- The same original polytabloid, with all prescribed component generators normalized
internally. -/
theorem witnessBalancePackingGenerator_coordinates (hd : delta ≤ 1)
    (v : witnessBalancePackingRowTuple hk z) :
    polytabloid z (witnessBalancePackingRowAssembly hk z hd v)=
      ∏ a, witnessBalanceComponentWord hk z a.val (v a) /
        witnessBalancePackingBaseCoefficient hk z a.val := by
  have he : partialRows hk z Finset.univ v=v := by
    funext a
    simp only [partialRows,Finset.mem_univ,if_true]
  simpa only [he] using generator_partialRows hk z hd v Finset.univ

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingBaseCoefficient
#print axioms HSTZ.witnessBalancePackingBaseCoefficient_ne_zero
#print axioms HSTZ.witnessBalancePackingRowAssembly
#print axioms HSTZ.witnessBalancePackingGenerator_coordinates
