import OAI.RepresentationTheory.Saxl.PieriRestriction

/-! Restriction with a fixed complement word, rather than summing it away.
The existing `wordRestrict` and its equivariance are reused unchanged. -/
namespace HSTZ
open OAI.Saxl
noncomputable section
attribute [local instance] Classical.propDecidable

def fixedComplement {a n e : ℕ} (i : Fin a ↪ Fin n) (c w : Fin n → Fin e) : Prop :=
  ∀ k, k ∉ Set.range i → w k = c k

def complementFilter {a n e : ℕ} (i : Fin a ↪ Fin n) (c : Fin n → Fin e) :
    WordSpace n e →ₗ[ℂ] WordSpace n e where
  toFun f w := if fixedComplement i c w then f w else 0
  map_add' _ _ := by ext w; simp only [Pi.add_apply]; split <;> simp
  map_smul' _ _ := by ext w; simp only [RingHom.id_apply, Pi.smul_apply]; split <;> simp

theorem complementFilter_equivariant {a n e : ℕ} (i : Fin a ↪ Fin n)
    (c : Fin n → Fin e) (g : Equiv.Perm (Fin n))
    (hg : ∀ k, k ∉ Set.range i → g k = k) (f : WordSpace n e) :
    complementFilter i c (wordRep n e g f) = wordRep n e g (complementFilter i c f) := by
  ext w
  have hp : fixedComplement i c (w ∘ g) ↔ fixedComplement i c w := by
    constructor
    · intro hw k hk
      simpa only [Function.comp_apply, hg k hk] using hw k hk
    · intro hw k hk
      simpa only [Function.comp_apply, hg k hk] using hw k hk
  change (if fixedComplement i c w then f (w ∘ g) else 0) =
    if fixedComplement i c (w ∘ g) then f (w ∘ g) else 0
  rw [hp]

def wordRestrictAt {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (c : Fin n → Fin e) : WordSpace n e →ₗ[ℂ] WordSpace a d :=
  (wordRestrict i j).comp (complementFilter i c)

theorem wordRestrictAt_coefficient {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (c : Fin n → Fin e) (b : Fin a → Fin d) (hc : c ∘ i = j ∘ b) (f : WordSpace n e) :
    wordRestrictAt i j c f b = f c := by
  classical
  change (∑ w : Fin n → Fin e, if w ∘ i = j ∘ b then
    (if fixedComplement i c w then f w else 0) else 0) = f c
  rw [Finset.sum_eq_single c]
  · simp [hc, fixedComplement]
  · intro w hw hwc
    by_cases hiw : w ∘ i = j ∘ b
    · by_cases hp : fixedComplement i c w
      · have he : w = c := by
          funext k
          by_cases hk : k ∈ Set.range i
          · obtain ⟨z, rfl⟩ := hk
            exact (congrFun hiw z).trans (congrFun hc z).symm
          · exact hp k hk
        exact (hwc he).elim
      · simp [hiw, hp]
    · simp [hiw]
  · simp

theorem wordRestrictAt_equivariant {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (c : Fin n → Fin e) (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a))
    (hi : ∀ k, g (i k) = i (h k)) (hg : ∀ k, k ∉ Set.range i → g k = k)
    (f : WordSpace n e) :
    wordRestrictAt i j c (wordRep n e g f) = wordRep a d h (wordRestrictAt i j c f) := by
  change wordRestrict i j (complementFilter i c (wordRep n e g f)) = _
  rw [complementFilter_equivariant i c g hg f]
  exact wordRestrict_equivariant i j g h hi (complementFilter i c f)

end
end HSTZ
#print axioms HSTZ.complementFilter_equivariant
#print axioms HSTZ.wordRestrictAt_coefficient
#print axioms HSTZ.wordRestrictAt_equivariant
