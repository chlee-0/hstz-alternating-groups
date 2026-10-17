import HSTZ.IntertwiningCompat
import HSTZ.TensorInterfaces
import HSTZ.WitnessBalanceSeparation
import HSTZ.InjectiveRangeLift

/-! Target-specific transfer to the full group from the projected component.
Adapts the `CyclicSector` averaging and `BalanceProjection` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0) to the HSTZ source and pair coordinates.
Averaging the raw lift keeps the original square image; stability under the
component projection is not asserted. The nonzero target map `f` is an explicit
hypothesis that is not proved here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

section
variable {k b delta n : ℕ} {nu : YoungDiagram} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (target : Tableau n nu)

private def balanceRawAverage
    (L : Representation.IntertwiningMap
      ((spechtRep target).comp (witnessBalanceGroup hk z).subtype)
      ((wordRep n (witnessBalancePairDim k b delta hk)).comp (witnessBalanceGroup hk z).subtype)) :
    Representation.IntertwiningMap (spechtRep target) (wordRep n (witnessBalancePairDim k b delta hk)) where
  toLinearMap := ∑ g : Equiv.Perm (Fin n),
    (wordRep n (witnessBalancePairDim k b delta hk) g).comp (L.toLinearMap.comp (spechtRep target g⁻¹))
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    change (∑ g : Equiv.Perm (Fin n),
      (wordRep n (witnessBalancePairDim k b delta hk) g).comp (L.toLinearMap.comp (spechtRep target g⁻¹)))
        (spechtRep target h x) = wordRep n _ h
      ((∑ g : Equiv.Perm (Fin n),
        (wordRep n (witnessBalancePairDim k b delta hk) g).comp (L.toLinearMap.comp (spechtRep target g⁻¹))) x)
    simp only [LinearMap.comp_apply,LinearMap.sum_apply,Representation.IntertwiningMap.toLinearMap_apply]
    rw [map_sum]
    apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
    apply Finset.sum_congr rfl
    intro g hg
    change wordRep n _ (h*g) (L (spechtRep target (h*g)⁻¹ (spechtRep target h x))) =
      wordRep n _ h (wordRep n _ g (L (spechtRep target g⁻¹ x)))
    simp only [mul_inv_rev,map_mul,Module.End.mul_apply]
    have he : spechtRep target h⁻¹ (spechtRep target h x)=x := by
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one]
      rfl
    rw [he]

private theorem balanceRawAverage_apply
    (L : Representation.IntertwiningMap
      ((spechtRep target).comp (witnessBalanceGroup hk z).subtype)
      ((wordRep n (witnessBalancePairDim k b delta hk)).comp (witnessBalanceGroup hk z).subtype))
    (x : Specht target) :
    balanceRawAverage hk z target L x =
      ∑ g : Equiv.Perm (Fin n), wordRep n _ g (L (spechtRep target g⁻¹ x)) := by
  change (∑ g : Equiv.Perm (Fin n),
    (wordRep n (witnessBalancePairDim k b delta hk) g).comp (L.toLinearMap.comp (spechtRep target g⁻¹))) x = _
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,Representation.IntertwiningMap.toLinearMap_apply]

private theorem balanceRawAverage_nonzero (hd : delta ≤ 1)
    (L : Representation.IntertwiningMap
      ((spechtRep target).comp (witnessBalanceGroup hk z).subtype)
      ((wordRep n (witnessBalancePairDim k b delta hk)).comp (witnessBalanceGroup hk z).subtype))
    (hs : ∀ x, L x ∈ witnessBalanceFixedOutputs hk z)
    (hn : (coordinateProjection (witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z)).comp L.toLinearMap ≠ 0) :
    balanceRawAverage hk z target L ≠ 0 := by
  classical
  let P := coordinateProjection (witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z)
  let Q := witnessBalanceGlobalProjection (k:=k) (b:=b) (delta:=delta) hk z
  let F := (witnessBalanceComponentProjection hk z
    (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
    (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).comp L
  have hP (x : Specht target) : P (F x)=F x := by
    funext w
    change (if witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w then
      (if witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w then L x w else 0) else 0) = _
    change (if witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w then
      (if witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w then L x w else 0) else 0) =
      (if witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w then L x w else 0)
    split_ifs <;> rfl
  have hkill (g : Equiv.Perm (Fin n)) (hg : g ∉ witnessBalanceGroup hk z) (x : Specht target) :
      P (wordRep n _ g (F x))=0 := by
    funext w
    change (if witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w then
      (if witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z (w ∘ g) then L x (w ∘ g) else 0) else 0)=0
    split_ifs with hw hwg
    · exfalso
      apply hg
      intro i
      exact (hw.2 (g i)).symm.trans (hwg.2 i)
    all_goals rfl
  have hterm (g : Equiv.Perm (Fin n)) (x : Specht target) :
      P (Q (wordRep n _ g (L (spechtRep target g⁻¹ x)))) =
        if g ∈ witnessBalanceGroup hk z then F x else 0 := by
    have hq : Q (wordRep n _ g (L (spechtRep target g⁻¹ x))) =
        wordRep n _ g (Q (L (spechtRep target g⁻¹ x))) :=
      Q.map_action g (L (spechtRep target g⁻¹ x))
    rw [hq]
    rw [witnessBalance_global_projection_eq (k:=k) (b:=b) (delta:=delta) hk z hd _ (hs _)]
    by_cases hg : g ∈ witnessBalanceGroup hk z
    · rw [if_pos hg]
      change P (wordRep n _ g (F (spechtRep target g⁻¹ x)))=F x
      have hF : F (spechtRep target g (spechtRep target g⁻¹ x)) =
          wordRep n _ g (F (spechtRep target g⁻¹ x)) :=
        F.map_action ⟨g,hg⟩ (spechtRep target g⁻¹ x)
      rw [←hF]
      have he : spechtRep target g (spechtRep target g⁻¹ x)=x := by
        rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one]
        rfl
      change P (F (spechtRep target g (spechtRep target g⁻¹ x)))=F x
      rw [he]
      exact hP x
    · rw [if_neg hg]
      exact hkill g hg _
  have hproj (x : Specht target) :
      P (Q (balanceRawAverage hk z target L x)) =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => g ∈ witnessBalanceGroup hk z)).card : ℂ) • F x := by
    rw [balanceRawAverage_apply]
    change P (Q.toLinearMap (∑ g : Equiv.Perm (Fin n), wordRep n _ g (L (spechtRep target g⁻¹ x)))) = _
    rw [map_sum Q.toLinearMap,map_sum P]
    change (∑ g : Equiv.Perm (Fin n), P (Q (wordRep n _ g (L (spechtRep target g⁻¹ x))))) = _
    have hh : (∑ g : Equiv.Perm (Fin n), P (Q (wordRep n _ g (L (spechtRep target g⁻¹ x))))) =
        ∑ g : Equiv.Perm (Fin n), if g ∈ witnessBalanceGroup hk z then F x else 0 :=
      Finset.sum_congr rfl (fun g hg => hterm g x)
    rw [hh]
    simp [Finset.sum_ite,Nat.cast_smul_eq_nsmul]
  have hc : ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => g ∈ witnessBalanceGroup hk z)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact ne_of_gt (Finset.card_pos.mpr ⟨1,by simp⟩)
  intro hz
  apply hn
  apply LinearMap.ext
  intro x
  have he := hproj x
  rw [hz] at he
  change P (Q.toLinearMap 0)=_ at he
  rw [Q.toLinearMap.map_zero,P.map_zero] at he
  exact (smul_eq_zero.mp he.symm).resolve_left hc

/-- Conditional on a nonzero restricted target map `f`, taken as a hypothesis.
The full-group averaging, the return to the range of the original square and
nonvanishing are derived. -/
theorem witnessBalance_square_map_of_projected (hd : delta ≤ 1)
    (f : Representation.IntertwiningMap
      ((spechtRep target).comp (witnessBalanceGroup hk z).subtype)
      (witnessBalanceProjectedRange hk z
        (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
        (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toRepresentation)
    (hf : f ≠ 0) :
    ∃ T : Representation.IntertwiningMap (spechtRep target) ((spechtRep z).tprod (spechtRep z)), T ≠ 0 := by
  letI : AddCommGroup (Specht z ⊗[ℂ] Specht z) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht z ⊗[ℂ] Specht z) := TensorProduct.leftModule
  obtain ⟨L,_,hs,hm,hn⟩ := witnessBalance_actual_raw_lift (k:=k) (b:=b) (delta:=delta) hk z hd target f hf
  let U : Representation.IntertwiningMap ((spechtRep z).tprod (spechtRep z))
      (wordRep n (witnessBalancePairDim k b delta hk)) :=
    (wordTensorIntertwiner n _ _).comp (spechtTensorInclusion z z)
  let W : Subrepresentation (wordRep n (witnessBalancePairDim k b delta hk)) :=
    { toSubmodule := U.toLinearMap.range
      apply_mem_toSubmodule := by
        intro g y hy
        obtain ⟨q,rfl⟩ := hy
        exact ⟨((spechtRep z).tprod (spechtRep z)) g q,U.map_action g q⟩ }
  let A := balanceRawAverage hk z target L
  have hA : A ≠ 0 := balanceRawAverage_nonzero hk z target hd L hs hn
  have hmem (x : Specht target) : A x ∈ W := by
    rw [show A x = _ from balanceRawAverage_apply hk z target L x]
    apply Submodule.sum_mem
    intro g hg
    exact W.apply_mem_toSubmodule g (hm _)
  let B : Representation.IntertwiningMap (spechtRep target) W.toRepresentation :=
    { toLinearMap := A.toLinearMap.codRestrict W.toSubmodule hmem
      isIntertwining' := fun g => LinearMap.ext <| fun x => Subtype.ext (A.map_action g x) }
  have hB : B ≠ 0 := by
    intro hz
    apply hA
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (congrArg (fun F => F x) hz)
  have hU : Function.Injective U :=
    (wordTensor n _ _).injective.comp (spechtTensorInclusion_injective z z)
  let I : Representation.IntertwiningMap W.toRepresentation ((spechtRep z).tprod (spechtRep z)) := injectiveRangeLift
    (R := ℂ) (G := Equiv.Perm (Fin n))
    (X := Specht z ⊗[ℂ] Specht z) (Y := WordSpace n (witnessBalancePairDim k b delta hk))
    (rho := (spechtRep z).tprod (spechtRep z))
    (sigma := wordRep n (witnessBalancePairDim k b delta hk)) U hU W
    (show W.toSubmodule ≤ U.toLinearMap.range from le_rfl)
  have hI : Function.Injective I := injectiveRangeLift_injective
    (R := ℂ) (G := Equiv.Perm (Fin n))
    (X := Specht z ⊗[ℂ] Specht z) (Y := WordSpace n (witnessBalancePairDim k b delta hk))
    (rho := (spechtRep z).tprod (spechtRep z))
    (sigma := wordRep n (witnessBalancePairDim k b delta hk)) U hU W
    (show W.toSubmodule ≤ U.toLinearMap.range from le_rfl)
  refine ⟨I.comp B,?_⟩
  intro hz
  apply hB
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hI
  have he := congrArg (fun F => F x) hz
  change I (B x)=0 at he
  exact he.trans I.toLinearMap.map_zero.symm

theorem witnessBalance_kronecker_pos_of_projected (hd : delta ≤ 1)
    (f : Representation.IntertwiningMap
      ((spechtRep target).comp (witnessBalanceGroup hk z).subtype)
      (witnessBalanceProjectedRange hk z
        (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
        (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toRepresentation)
    (hf : f ≠ 0) : 0 < kronecker z z target :=
  (kronecker_pos_iff z z target).mpr (witnessBalance_square_map_of_projected hk z target hd f hf)

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_square_map_of_projected
#print axioms HSTZ.witnessBalance_kronecker_pos_of_projected
