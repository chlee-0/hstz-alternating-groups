import Mathlib.RepresentationTheory.Basic

/-! The permutation representation of `G` on finitely supported functions `X →₀ R`.
`finsuppAction_native` identifies it with Mathlib's `Representation.ofMulAction` on
`MonoidAlgebra R X` via `MonoidAlgebra.coeffLinearEquiv`. -/
namespace HSTZ
noncomputable section

def finsuppAction (R G X : Type*) [Semiring R] [Monoid G] [MulAction G X] :
    Representation R G (X →₀ R) where
  toFun g := Finsupp.lmapDomain R R (g • ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

theorem finsuppAction_def {R G X : Type*} [Semiring R] [Monoid G] [MulAction G X]
    (g : G) : finsuppAction R G X g = Finsupp.lmapDomain R R (g • ·) := rfl

@[simp] theorem finsuppAction_single {R G X : Type*} [Semiring R] [Monoid G]
    [MulAction G X] (g : G) (x : X) (r : R) :
    finsuppAction R G X g (Finsupp.single x r) = Finsupp.single (g • x) r := by
  simp [finsuppAction]

theorem finsuppAction_native {R G X : Type*} [Semiring R] [Monoid G]
    [MulAction G X] (g : G) (v : MonoidAlgebra R X) :
    (MonoidAlgebra.coeffLinearEquiv R) (Representation.ofMulAction R G X g v) =
      finsuppAction R G X g ((MonoidAlgebra.coeffLinearEquiv R) v) := by
  simp [Representation.ofMulAction_def, finsuppAction]

@[simp] theorem finsuppAction_apply {R G X : Type*} [Semiring R] [Group G]
    [MulAction G X] (g : G) (f : X →₀ R) (x : X) :
    finsuppAction R G X g f x = f (g⁻¹ • x) := by
  have h := Representation.coeff_ofMulAction (k := R) g
    ((MonoidAlgebra.coeffLinearEquiv R).symm f) x
  simpa [Representation.ofMulAction_def, finsuppAction] using h

end
end HSTZ

#print axioms HSTZ.finsuppAction_native
#print axioms HSTZ.finsuppAction_apply
