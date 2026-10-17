import HSTZ.TauCetiFinite.IndexedCertificate
import HSTZ.TauCetiFinite.ExplicitClasses

/-! Indexed character rows and the norm and cover sums (D and E) over a complete class
catalog. All references are checked against both keys, and missing or extra class
entries make the check fail. The only character input is the checked indexed table
together with `agreementThrough15`. `RestrictionNorm` and `EvenMultiplicity` supply the
representation-theoretic identities. -/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

def checkQuery (t : IndexedTable) (lam rho : Shape) (d : ℕ) : Bool :=
  match indexedGet t d with
  | none => false
  | some e => decide (e.entry.shape = lam ∧ e.entry.cycles = rho)

def indexedValue (t : IndexedTable) (d : ℕ) : ℤ :=
  ((indexedGet t d).map (fun e => e.entry.value)).getD 0

def checkIndexedRow (t : IndexedTable) (lam : Shape) : List Shape → List ℕ → Bool
  | [], [] => true
  | rho::rs, d::ds => checkQuery t lam rho d && checkIndexedRow t lam rs ds
  | _, _ => false

def normTerm (n : ℕ) (rho : Shape) (v : ℤ) : ℤ :=
  if (n-rho.length)%2 = 0 then ((n.factorial / shapeZ rho : ℕ) : ℤ) * v^2 else 0

def coverTerm (n : ℕ) (rho : Shape) (v w : ℤ) : ℤ :=
  if (n-rho.length)%2 = 0 then ((n.factorial / shapeZ rho : ℕ) : ℤ) * v^2*w else 0

def indexedNormSum (t : IndexedTable) (n : ℕ) : List Shape → List ℕ → ℤ
  | [], [] => 0
  | rho::rs, d::ds => normTerm n rho (indexedValue t d) + indexedNormSum t n rs ds
  | _, _ => 0

def indexedCoverSum (t : IndexedTable) (n : ℕ) : List Shape → List ℕ → List ℕ → ℤ
  | [], [], [] => 0
  | rho::rs, d::ds, e::es => coverTerm n rho (indexedValue t d) (indexedValue t e) +
      indexedCoverSum t n rs ds es
  | _, _, _ => 0

theorem checkQuery_value (t : IndexedTable) (ht : checkIndexedTable t = true)
    (lam rho : Shape) (d : ℕ) (hq : checkQuery t lam rho d = true) :
    indexedValue t d = mn lam rho := by
  cases he : indexedGet t d with
  | none => simp [checkQuery, he] at hq
  | some e =>
    have hk : e.entry.shape = lam ∧ e.entry.cycles = rho := by
      simpa only [checkQuery, he, decide_eq_true_eq] using hq
    simpa [indexedValue, he, hk.1, hk.2] using indexedTable_sound t ht d e he

theorem indexedNormSum_eq (t : IndexedTable) (ht : checkIndexedTable t = true)
    (n : ℕ) (lam : Shape) (classes : List Shape) (refs : List ℕ)
    (hr : checkIndexedRow t lam classes refs = true) :
    indexedNormSum t n classes refs =
      (classes.map (fun rho => normTerm n rho (mn lam rho))).sum := by
  induction classes generalizing refs with
  | nil => cases refs <;> simp_all [checkIndexedRow, indexedNormSum]
  | cons rho rs ih =>
    cases refs with
    | nil => simp [checkIndexedRow] at hr
    | cons d ds =>
      have hh : checkQuery t lam rho d = true ∧ checkIndexedRow t lam rs ds = true := by
        simpa only [checkIndexedRow, Bool.and_eq_true] using hr
      simp only [indexedNormSum, List.map_cons, List.sum_cons]
      rw [checkQuery_value t ht lam rho d hh.1, ih ds hh.2]

theorem indexedCoverSum_eq (t : IndexedTable) (ht : checkIndexedTable t = true)
    (n : ℕ) (lam nu : Shape) (classes : List Shape) (a b : List ℕ)
    (ha : checkIndexedRow t lam classes a = true)
    (hb : checkIndexedRow t nu classes b = true) :
    indexedCoverSum t n classes a b =
      (classes.map (fun rho => coverTerm n rho (mn lam rho) (mn nu rho))).sum := by
  induction classes generalizing a b with
  | nil => cases a <;> cases b <;> simp_all [checkIndexedRow, indexedCoverSum]
  | cons rho rs ih =>
    cases a with
    | nil => simp [checkIndexedRow] at ha
    | cons d ds =>
      cases b with
      | nil => simp [checkIndexedRow] at hb
      | cons e es =>
        have hh : checkQuery t lam rho d = true ∧ checkIndexedRow t lam rs ds = true := by
          simpa only [checkIndexedRow, Bool.and_eq_true] using ha
        have hh' : checkQuery t nu rho e = true ∧ checkIndexedRow t nu rs es = true := by
          simpa only [checkIndexedRow, Bool.and_eq_true] using hb
        simp only [indexedCoverSum, List.map_cons, List.sum_cons]
        rw [checkQuery_value t ht lam rho d hh.1, checkQuery_value t ht nu rho e hh'.1,
          ih ds es hh.2 hh'.2]

theorem indexedNorm_eq_evenNorm {n : ℕ} (hn : n ≤ 15) (t : IndexedTable)
    (ht : checkIndexedTable t = true) (classes : List Shape) (hc : checkClasses n classes = true)
    (lam : Nat.Partition n) (refs : List ℕ)
    (hr : checkIndexedRow t (partitionRows lam) classes refs = true) :
    2 * indexedNormSum t n classes refs = evenNormNumerator lam := by
  classical
  rw [indexedNormSum_eq t ht n (partitionRows lam) classes refs hr,
    checkClasses_sum classes hc]
  unfold evenNormNumerator
  congr 1
  apply Finset.sum_congr rfl
  intro rho hrho
  unfold normTerm
  rw [partitionRows_length, shapeZ_partitionRows, agreementThrough15 n hn lam rho]
  by_cases he : (n-rho.parts.card)%2 = 0 <;> simp [EvenCycleShape, he]

theorem indexedCover_eq_evenCover {n : ℕ} (hn : n ≤ 15) (t : IndexedTable)
    (ht : checkIndexedTable t = true) (classes : List Shape) (hc : checkClasses n classes = true)
    (lam nu : Nat.Partition n) (a b : List ℕ)
    (ha : checkIndexedRow t (partitionRows lam) classes a = true)
    (hb : checkIndexedRow t (partitionRows nu) classes b = true) :
    2 * indexedCoverSum t n classes a b = evenCoverNumerator lam nu := by
  classical
  rw [indexedCoverSum_eq t ht n (partitionRows lam) (partitionRows nu) classes a b ha hb,
    checkClasses_sum classes hc]
  unfold evenCoverNumerator
  congr 1
  apply Finset.sum_congr rfl
  intro rho hrho
  unfold coverTerm
  rw [partitionRows_length, shapeZ_partitionRows, agreementThrough15 n hn lam rho,
    agreementThrough15 n hn nu rho]
  by_cases he : (n-rho.parts.card)%2 = 0 <;> simp [EvenCycleShape, he]

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.checkQuery_value
#print axioms HSTZ.TauCetiFinite.indexedNormSum_eq
#print axioms HSTZ.TauCetiFinite.indexedCoverSum_eq
#print axioms HSTZ.TauCetiFinite.indexedNorm_eq_evenNorm
#print axioms HSTZ.TauCetiFinite.indexedCover_eq_evenCover
