import HSTZ.TauCetiFinite.ExplicitClasses

/-!
Lemmas for assembling the facts required by `checkClasses` from short pieces.
Each use must prove duplicate-freeness, validity, disjointness of the pieces and the
exact count.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

theorem catalog_nodup_append (xs ys : List Shape)
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : List.Disjoint xs ys) :
    (xs ++ ys).Nodup :=
  List.Nodup.append hx hy hd

theorem catalog_valid_append (n : ℕ) (xs ys : List Shape)
    (hx : ∀ s ∈ xs, IsShape s ∧ s.sum = n)
    (hy : ∀ s ∈ ys, IsShape s ∧ s.sum = n) :
    ∀ s ∈ xs ++ ys, IsShape s ∧ s.sum = n := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact hx s hs
  · exact hy s hs

/-- Assemble separately proved facts into the catalog check `checkClasses`. -/
theorem checkClasses_of_facts (n : ℕ) (xs : List Shape)
    (hn : xs.Nodup) (hv : ∀ s ∈ xs, IsShape s ∧ s.sum = n)
    (hc : xs.length = partitionCount n n n) : checkClasses n xs = true := by
  simp only [checkClasses, decide_eq_true_eq]
  exact ⟨hn, hv, hc⟩

end HSTZ.TauCetiFinite

#print axioms HSTZ.TauCetiFinite.catalog_nodup_append
#print axioms HSTZ.TauCetiFinite.catalog_valid_append
#print axioms HSTZ.TauCetiFinite.checkClasses_of_facts
