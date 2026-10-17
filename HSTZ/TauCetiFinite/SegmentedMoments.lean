import HSTZ.TauCetiFinite.IndexedMoments

/-!
Splits the indexed row checker and the integer moment sums along list appends.
Equal prefix lengths ensure that each simultaneous recursion reaches the append
boundary together. No condition on the suffix is needed.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

theorem indexedNormSum_append (t : IndexedTable) (n : ℕ)
    (xs ys : List Shape) (a b : List ℕ) (ha : xs.length = a.length) :
    indexedNormSum t n (xs ++ ys) (a ++ b) =
      indexedNormSum t n xs a + indexedNormSum t n ys b := by
  induction xs generalizing a with
  | nil =>
    cases a with
    | nil => simp [indexedNormSum]
    | cons d ds => simp at ha
  | cons rho xs ih =>
    cases a with
    | nil => simp at ha
    | cons d ds =>
      have htail : xs.length = ds.length := by simpa using ha
      simp only [List.cons_append, indexedNormSum, ih ds htail, add_assoc]

theorem indexedCoverSum_append (t : IndexedTable) (n : ℕ)
    (xs ys : List Shape) (a b c d : List ℕ)
    (ha : xs.length = a.length) (hc : xs.length = c.length) :
    indexedCoverSum t n (xs ++ ys) (a ++ b) (c ++ d) =
      indexedCoverSum t n xs a c + indexedCoverSum t n ys b d := by
  induction xs generalizing a c with
  | nil =>
    cases a with
    | cons i asTail => simp at ha
    | nil =>
      cases c with
      | nil => simp [indexedCoverSum]
      | cons j js => simp at hc
  | cons rho xs ih =>
    cases a with
    | nil => simp at ha
    | cons i asTail =>
      cases c with
      | nil => simp at hc
      | cons j js =>
        have hatail : xs.length = asTail.length := by simpa using ha
        have hctail : xs.length = js.length := by simpa using hc
        simp only [List.cons_append, indexedCoverSum,
          ih asTail js hatail hctail, add_assoc]

theorem checkIndexedRow_append (t : IndexedTable) (lam : Shape)
    (xs ys : List Shape) (a b : List ℕ) (ha : xs.length = a.length) :
    checkIndexedRow t lam (xs ++ ys) (a ++ b) =
      (checkIndexedRow t lam xs a && checkIndexedRow t lam ys b) := by
  induction xs generalizing a with
  | nil =>
    cases a with
    | nil => simp [checkIndexedRow]
    | cons d ds => simp at ha
  | cons rho xs ih =>
    cases a with
    | nil => simp at ha
    | cons d ds =>
      have htail : xs.length = ds.length := by simpa using ha
      simp only [List.cons_append, checkIndexedRow, ih ds htail, Bool.and_assoc]

end HSTZ.TauCetiFinite

#print axioms HSTZ.TauCetiFinite.indexedNormSum_append
#print axioms HSTZ.TauCetiFinite.indexedCoverSum_append
#print axioms HSTZ.TauCetiFinite.checkIndexedRow_append
