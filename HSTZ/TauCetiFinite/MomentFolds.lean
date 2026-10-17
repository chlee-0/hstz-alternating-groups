import HSTZ.TauCetiFinite.ClassEnumeration
import HSTZ.TauCetiFinite.EvenMoments

/-!
Executable norm and cover sums (D and E) over the complete canonical class set, using
cached certificate values. Rows with missing entries are rejected before cached values
are used, so the default value below never stands in for a missing entry.
These are character-sum identities, not representation multiplicity identities.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

def shapeZ (xs : Shape) : ℕ :=
  ∏ i ∈ xs.toFinset, i ^ xs.count i * (xs.count i).factorial

def cachedValue (cert : Certificate) (lam rho : Shape) : ℤ :=
  (lookup cert lam rho).getD 0

/-- All canonical classes must be present, including the identity and fixed-point classes. -/
def classRowPresent (cert : Certificate) (n : ℕ) (lam : Shape) : Bool :=
  decide (∀ rho ∈ partitionShapes n n n, (lookup cert lam rho).isSome = true)

def cachedNorm (cert : Certificate) (n : ℕ) (lam : Shape) : ℤ :=
  2 * ∑ rho ∈ partitionShapes n n n,
    if (n-rho.length) % 2 = 0 then
      ((n.factorial / shapeZ rho : ℕ) : ℤ) * cachedValue cert lam rho ^ 2 else 0

def cachedCover (cert : Certificate) (n : ℕ) (lam nu : Shape) : ℤ :=
  2 * ∑ rho ∈ partitionShapes n n n,
    if (n-rho.length) % 2 = 0 then
      ((n.factorial / shapeZ rho : ℕ) : ℤ) * cachedValue cert lam rho ^ 2 *
        cachedValue cert nu rho else 0

theorem shapeZ_partitionRows {n : ℕ} (p : Nat.Partition n) :
    shapeZ (partitionRows p) = TauCeti.zPart p := by
  unfold TauCeti.zPart TauCeti.partMultiplicity
  rw [← partitionRows_parts p]
  simp [shapeZ]

theorem partitionRows_length {n : ℕ} (p : Nat.Partition n) :
    (partitionRows p).length = p.parts.card := by
  simpa using congrArg Multiset.card (partitionRows_parts p)

/-- A verified certificate with a complete row supplies Specht character values. -/
theorem cachedValue_character {n : ℕ} (hn : n ≤ 15) (cert : Certificate)
    (lam rho : Nat.Partition n) (hv : verify cert = true)
    (hp : classRowPresent cert n (partitionRows lam) = true) :
    cachedValue cert (partitionRows lam) (partitionRows rho) =
      TauCeti.spechtCharValue lam rho := by
  have hall := of_decide_eq_true hp
  have hs := hall (partitionRows rho) (partitionRows_mem_partitionShapes rho)
  cases he : lookup cert (partitionRows lam) (partitionRows rho) with
  | none => simp [he] at hs
  | some value =>
    unfold cachedValue
    rw [he]
    exact (lookup_sound (verify_sound cert hv) he).trans
      (agreementThrough15 n hn lam rho)

/-- The cached norm sum is `evenNormNumerator`; every class is summed once with its
full weight. -/
theorem cachedNorm_eq_evenNorm {n : ℕ} (hn : n ≤ 15) (cert : Certificate)
    (lam : Nat.Partition n) (hv : verify cert = true)
    (hp : classRowPresent cert n (partitionRows lam) = true) :
    cachedNorm cert n (partitionRows lam) = evenNormNumerator lam := by
  classical
  unfold cachedNorm
  rw [sum_partitionShapes]
  unfold evenNormNumerator
  congr 1
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [partitionRows_length, shapeZ_partitionRows,
    cachedValue_character hn cert lam rho hv hp]
  by_cases he : (n - rho.parts.card) % 2 = 0 <;> simp [EvenCycleShape, he]

/-- The cached cover sum is `evenCoverNumerator`. -/
theorem cachedCover_eq_evenCover {n : ℕ} (hn : n ≤ 15) (cert : Certificate)
    (lam nu : Nat.Partition n) (hv : verify cert = true)
    (hlam : classRowPresent cert n (partitionRows lam) = true)
    (hnu : classRowPresent cert n (partitionRows nu) = true) :
    cachedCover cert n (partitionRows lam) (partitionRows nu) =
      evenCoverNumerator lam nu := by
  classical
  unfold cachedCover
  rw [sum_partitionShapes]
  unfold evenCoverNumerator
  congr 1
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [partitionRows_length, shapeZ_partitionRows,
    cachedValue_character hn cert lam rho hv hlam,
    cachedValue_character hn cert nu rho hv hnu]
  by_cases he : (n - rho.parts.card) % 2 = 0 <;> simp [EvenCycleShape, he]

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.shapeZ_partitionRows
#print axioms HSTZ.TauCetiFinite.partitionRows_length
#print axioms HSTZ.TauCetiFinite.cachedValue_character
#print axioms HSTZ.TauCetiFinite.cachedNorm_eq_evenNorm
#print axioms HSTZ.TauCetiFinite.cachedCover_eq_evenCover
