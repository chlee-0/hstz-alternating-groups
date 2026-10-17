import HSTZ.PositionPairBlock

/-! Compatibility of block and core permutations. -/
namespace HSTZ
/-- The block's first permutation is precisely the pointwise-complement-fixed
embedding used by contained branching. -/
theorem sumPermHom_core {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) :
    sumPermHom e (g,1) = g.viaEmbedding (blockInclusion e) := by
  apply Equiv.ext
  intro k
  obtain ⟨z,rfl⟩ := e.symm.surjective k
  cases z with
  | inl j =>
    calc
      _ = blockInclusion e (g j) := OAI.Saxl.sumPerm_left e g 1 j
      _ = g.viaEmbedding (blockInclusion e) (blockInclusion e j) :=
        (Equiv.Perm.viaEmbedding_apply g (blockInclusion e) j).symm
  | inr j =>
    have hk : e.symm (Sum.inr j) ∉ Set.range (blockInclusion e) := by
      rw [blockInclusion_range e]
      simp
    calc
      _ = e.symm (Sum.inr j) := OAI.Saxl.sumPerm_right e g 1 j
      _ = g.viaEmbedding (blockInclusion e) (e.symm (Sum.inr j)) :=
        (Equiv.Perm.viaEmbedding_apply_of_notMem g (blockInclusion e) _ hk).symm

end HSTZ
#print axioms HSTZ.sumPermHom_core
