import HSTZ.BalanceNeighboringPositions
import HSTZ.OneRowTableau
import HSTZ.OneRowTensor

/-! One-column constant-output support. The local claim follows
`Balance/ConstantOutputs` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0);
the proof here uses the full-column sign action and one-row evaluation. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def balanceSingletonTableau (n : ℕ) : Tableau n (oneRowDiagram n).transpose where
  toFun i := ⟨(i.val,0), YoungDiagram.mem_transpose.mpr (by simp [i.isLt])⟩
  invFun c := ⟨c.val.1, by
    have hc := YoungDiagram.mem_transpose.mp c.property
    change (c.val.2,c.val.1)∈oneRowDiagram n at hc
    exact (mem_oneRowDiagram.mp hc).2⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv c := by
    have hc := YoungDiagram.mem_transpose.mp c.property
    change (c.val.2,c.val.1)∈oneRowDiagram n at hc
    have hc' : c.val.2=0 ∧ c.val.1<n := mem_oneRowDiagram.mp hc
    apply Subtype.ext
    exact Prod.ext rfl hc'.1.symm

theorem balanceSingleton_full_column_group (n : ℕ) :
    columnGroup (balanceSingletonTableau n)=⊤ := by
  apply Subgroup.ext
  intro g
  change (∀ i, (balanceSingletonTableau n (g i)).val.2=
    (balanceSingletonTableau n i).val.2) ↔ True
  constructor
  · intro _; trivial
  · intro _ i; rfl

def balanceSingletonReverse (n : ℕ) : columnGroup (balanceSingletonTableau n) :=
  ⟨Fin.revPerm, by rw [balanceSingleton_full_column_group]; trivial⟩

def balanceSingletonPair (n : ℕ) :=
  mergeWords (rowWord (balanceSingletonTableau n))
    (rowWord (balanceSingletonTableau n) ∘ (balanceSingletonReverse n).val)

theorem balanceSingleton_pair_survives (n : ℕ) :
    balanceInOutputs ({n} : Set ℕ) (balanceSingletonPair n) := by
  intro i
  simp only [balanceSingletonPair,mergeWords,balancePairOutput,
    Equiv.symm_apply_apply,Set.mem_singleton_iff]
  change i.val+i.rev.val+1=n
  simp only [Fin.val_rev]
  have hi := i.isLt
  omega

def balanceSingletonRepeated (n : ℕ) :=
  wordTensor n ((oneRowDiagram n).transpose.colLen 0)
    ((oneRowDiagram n).transpose.colLen 0)
    (polytabloid (balanceSingletonTableau n) ⊗ₜ[ℂ]
      polytabloid (balanceSingletonTableau n))

def balanceSingletonProjected (n : ℕ) :=
  coordinateProjection (balanceInOutputs ({n} : Set ℕ)) (balanceSingletonRepeated n)

theorem balanceSingleton_projected_coefficient (n : ℕ) :
    balanceSingletonProjected n (balanceSingletonPair n)=
      signC (balanceSingletonReverse n).val := by
  classical
  rw [balanceSingletonProjected,coordinateProjection_apply,
    if_pos (balanceSingleton_pair_survives n)]
  rw [balanceSingletonRepeated,wordTensor_tmul]
  simp only [balanceSingletonPair,splitLeft_merge,splitRight_merge]
  rw [polytabloid_rowWord,polytabloid_column_coeff,one_mul]

theorem balanceSingleton_projected_ne_zero (n : ℕ) :
    balanceSingletonProjected n≠0 := by
  intro h
  have hc := congrFun h (balanceSingletonPair n)
  rw [balanceSingleton_projected_coefficient] at hc
  have hs := signC_mul_self (balanceSingletonReverse n).val
  change signC (balanceSingletonReverse n).val=0 at hc
  rw [hc,zero_mul] at hs
  exact zero_ne_one hs

theorem balanceSingleton_repeated_fixed (n : ℕ) (g : Equiv.Perm (Fin n)) :
    wordRep n _ g (balanceSingletonRepeated n)=balanceSingletonRepeated n := by
  let h : columnGroup (balanceSingletonTableau n) :=
    ⟨g,by rw [balanceSingleton_full_column_group]; trivial⟩
  have hp := polytabloid_alternating (balanceSingletonTableau n) h
  funext w
  change balanceSingletonRepeated n (w ∘ g)=balanceSingletonRepeated n w
  rw [balanceSingletonRepeated,wordTensor_tmul,wordTensor_tmul]
  have hl := congrFun hp (splitLeft w)
  have hr := congrFun hp (splitRight w)
  change polytabloid (balanceSingletonTableau n) (splitLeft w ∘ g)=
    signC g*polytabloid (balanceSingletonTableau n) (splitLeft w) at hl
  change polytabloid (balanceSingletonTableau n) (splitRight w ∘ g)=
    signC g*polytabloid (balanceSingletonTableau n) (splitRight w) at hr
  rw [show splitLeft (w ∘ g)=splitLeft w ∘ g from rfl,
    show splitRight (w ∘ g)=splitRight w ∘ g from rfl,hl,hr]
  calc
    _ = (signC g*signC g)*(polytabloid (balanceSingletonTableau n) (splitLeft w)*
      polytabloid (balanceSingletonTableau n) (splitRight w)) := by ring
    _ = _ := by rw [signC_mul_self,one_mul]

theorem balanceSingleton_projected_fixed (n : ℕ) (g : Equiv.Perm (Fin n)) :
    wordRep n _ g (balanceSingletonProjected n)=balanceSingletonProjected n := by
  classical
  funext w
  have hz := congrFun (balanceSingleton_repeated_fixed n g) w
  change balanceSingletonRepeated n (w ∘ g)=balanceSingletonRepeated n w at hz
  change (if balanceInOutputs ({n} : Set ℕ) (w ∘ g)
    then balanceSingletonRepeated n (w ∘ g) else 0)=
    (if balanceInOutputs ({n} : Set ℕ) w then balanceSingletonRepeated n w else 0)
  rw [balanceInOutputs_invariant,hz]

/-- Singleton support, for every source tableau and every degree, including degree 0.
The prescribed pair, the nonzero invariant and the map are constructed in the proof. -/
theorem balanceSingleton_projected_support (n : ℕ)
    (t : Tableau n (oneRowDiagram n).transpose) :
    ∃ J : Representation.IntertwiningMap (spechtRep (oneRowTableau n))
      (balanceProjectedSquare t (balanceInOutputs ({n} : Set ℕ))
        (balanceInOutputs_invariant ({n} : Set ℕ))).toRepresentation,
      Function.Injective J := by
  classical
  let W := balanceProjectedSquare t (balanceInOutputs ({n} : Set ℕ))
    (balanceInOutputs_invariant ({n} : Set ℕ))
  let p : Specht t := ⟨polytabloid (balanceSingletonTableau n),
    polytabloid_mem_all t (balanceSingletonTableau n)⟩
  have hy : balanceSingletonProjected n∈W.toSubmodule :=
    ⟨p ⊗ₜ[ℂ] p,rfl⟩
  let y : W.toSubmodule := ⟨balanceSingletonProjected n,hy⟩
  have hfixed (g : Equiv.Perm (Fin n)) : W.toRepresentation g y=y := by
    apply Subtype.ext
    exact balanceSingleton_projected_fixed n g
  let J : Representation.IntertwiningMap (spechtRep (oneRowTableau n)) W.toRepresentation :=
    { toLinearMap :=
        { toFun := fun x => oneRowEvaluation (oneRowTableau n) x • y
          map_add' := by intro x z; simp only [map_add,add_smul]
          map_smul' := by intro a x; simp only [map_smul,smul_smul]; rfl }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        change oneRowEvaluation (oneRowTableau n) (spechtRep (oneRowTableau n) g x) • y =
          W.toRepresentation g (oneRowEvaluation (oneRowTableau n) x • y)
        rw [oneRow_specht_fixed (oneRowTableau n) (oneRowDiagram_rows n)]
        rw [map_smul,hfixed] }
  have hJ : J≠0 := by
    intro h
    let v : Specht (oneRowTableau n) := ⟨polytabloid (oneRowTableau n),mem_cyclic _ _⟩
    have hv := DFunLike.congr_fun h v
    change oneRowEvaluation (oneRowTableau n) v • y=0 at hv
    have he : oneRowEvaluation (oneRowTableau n) v=1 :=
      polytabloid_rowWord (oneRowTableau n)
    rw [he,one_smul] at hv
    have hz := congrArg Subtype.val hv
    exact balanceSingleton_projected_ne_zero n hz
  letI := specht_irreducible (oneRowTableau n)
  exact ⟨J,(Representation.IsIrreducible.injective_or_eq_zero J).resolve_right hJ⟩

end
end HSTZ
#print axioms HSTZ.balanceSingletonTableau
#print axioms HSTZ.balanceSingleton_full_column_group
#print axioms HSTZ.balanceSingleton_pair_survives
#print axioms HSTZ.balanceSingleton_projected_coefficient
#print axioms HSTZ.balanceSingleton_projected_ne_zero
#print axioms HSTZ.balanceSingleton_repeated_fixed
#print axioms HSTZ.balanceSingleton_projected_fixed
#print axioms HSTZ.balanceSingleton_projected_support
