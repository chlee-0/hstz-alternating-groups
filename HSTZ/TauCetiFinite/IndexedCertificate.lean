import HSTZ.TauCetiFinite.Agreement

/-!
An indexed certificate checker for the Murnaghan–Nakayama recurrence, separate from
the linear-list checker in `HSTZ.MurnaghanNakayama.Certificate`. Every bead move is
regenerated; each explicit reference must point strictly backward and match both keys.
Missing, extra or cyclic dependencies make the check fail, and correctness of the
certificate producer is not assumed. The data are split into fixed-size blocks to keep
source size and reduction depth within compiler limits.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

structure IndexedEntry where
  entry : Entry
  dependencies : List ℕ
  deriving DecidableEq, Repr

def indexedSum (get : ℕ → Option IndexedEntry) (i : ℕ) (rho : Shape) :
    List Move → List ℕ → Option ℤ
  | [], [] => some 0
  | m::ms, d::ds =>
      if d < i then
        match get d, indexedSum get i rho ms ds with
        | some e, some b =>
            if e.entry.shape = m.shape ∧ e.entry.cycles = rho then
              some (legSign m.leg * e.entry.value + b)
            else none
        | _, _ => none
      else none
  | _, _ => none

def indexedStep (get : ℕ → Option IndexedEntry) (i : ℕ) (e : IndexedEntry) : Option ℤ :=
  match e.entry.cycles with
  | [] => if e.dependencies = [] then some (baseValue e.entry.shape) else none
  | r::rho => indexedSum get i rho (moves e.entry.shape r) e.dependencies

def checkIndexedEntry (get : ℕ → Option IndexedEntry) (i : ℕ) (e : IndexedEntry) : Bool :=
  decide (indexedStep get i e = some e.entry.value)

theorem indexedSum_sound (get : ℕ → Option IndexedEntry) (i : ℕ) (rho : Shape)
    (hc : ∀ d < i, ∀ e, get d = some e → e.entry.value = mn e.entry.shape e.entry.cycles)
    (ms : List Move) (refs : List ℕ) : ∀ v,
    indexedSum get i rho ms refs = some v →
      v = weightedSum (fun mu => mn mu rho) ms := by
  induction ms generalizing refs with
  | nil =>
    cases refs with
    | nil => intro v hv; simpa [indexedSum, weightedSum] using hv.symm
    | cons d ds => intro v hv; simp [indexedSum] at hv
  | cons m ms ih =>
    cases refs with
    | nil => intro v hv; simp [indexedSum] at hv
    | cons d ds =>
      intro v hv
      by_cases hd : d < i
      · cases he : get d with
        | none => simp [indexedSum, hd, he] at hv
        | some e =>
          cases hb : indexedSum get i rho ms ds with
          | none => simp [indexedSum, hd, he, hb] at hv
          | some b =>
            by_cases hk : e.entry.shape = m.shape ∧ e.entry.cycles = rho
            · have hh : legSign m.leg * e.entry.value + b = v := by
                simpa [indexedSum, hd, he, hb, hk] using hv
              calc
                v = legSign m.leg * e.entry.value + b := hh.symm
                _ = legSign m.leg * mn m.shape rho +
                    weightedSum (fun mu => mn mu rho) ms := by
                  rw [hc d hd e he, hk.1, hk.2, ih ds b hb]
                _ = _ := rfl
            · simp [indexedSum, hd, he, hb, hk] at hv
      · simp [indexedSum, hd] at hv

/-- If every present entry passes its check, every entry stores the recurrence value. -/
theorem indexedCheck_sound (get : ℕ → Option IndexedEntry)
    (hv : ∀ i e, get i = some e → checkIndexedEntry get i e = true) :
    ∀ i e, get i = some e → e.entry.value = mn e.entry.shape e.entry.cycles := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro e he
    have hs : indexedStep get i e = some e.entry.value := of_decide_eq_true (hv i e he)
    cases hr : e.entry.cycles with
    | nil =>
      by_cases hd : e.dependencies = []
      · simpa [indexedStep, hr, hd, mn_nil] using hs.symm
      · simp [indexedStep, hr, hd] at hs
    | cons r rho =>
      rw [mn_cons]
      apply indexedSum_sound get i rho (fun d hd e he => ih d hd e he)
        (moves e.entry.shape r) e.dependencies e.entry.value
      simpa [indexedStep, hr] using hs

/-- Entries stored in blocks of 16; dependency references use global indices. -/
structure IndexedTable where
  bound : ℕ
  block : ℕ → Array IndexedEntry

def indexedGet (t : IndexedTable) (i : ℕ) : Option IndexedEntry :=
  if i < t.bound then (t.block (i/16))[i%16]? else none

def checkIndexedBlock (t : IndexedTable) (k : ℕ) : Bool :=
  (List.range 16).all fun j =>
    match indexedGet t (k*16+j) with
    | none => true
    | some e => checkIndexedEntry (indexedGet t) (k*16+j) e

def checkIndexedGroup (t : IndexedTable) (g : ℕ) : Bool :=
  (List.range 16).all fun k => checkIndexedBlock t (g*16+k)

def checkIndexedTable (t : IndexedTable) : Bool :=
  (List.range (t.bound/256+1)).all (checkIndexedGroup t)

/-- A passing table check gives the pointwise check at every present entry. -/
theorem indexedTable_checks (t : IndexedTable) (ht : checkIndexedTable t = true) :
    ∀ i e, indexedGet t i = some e → checkIndexedEntry (indexedGet t) i e = true := by
  intro i e he
  have hib : i < t.bound := by
    by_contra hn
    simp [indexedGet, hn] at he
  have hk : i/256 < t.bound/256+1 := by omega
  have hj : (i/16)%16 < 16 := Nat.mod_lt _ (by decide)
  have hj' : i%16 < 16 := Nat.mod_lt _ (by decide)
  have hg := List.all_eq_true.mp ht (i/256) (List.mem_range.mpr hk)
  have hb := List.all_eq_true.mp hg ((i/16)%16) (List.mem_range.mpr hj)
  have hx := List.all_eq_true.mp hb (i%16) (List.mem_range.mpr hj')
  have hi : (i/256*16+(i/16)%16)*16+i%16 = i := by omega
  rw [hi, he] at hx
  exact hx

theorem indexedTable_sound (t : IndexedTable) (ht : checkIndexedTable t = true) :
    ∀ i e, indexedGet t i = some e → e.entry.value = mn e.entry.shape e.entry.cycles :=
  indexedCheck_sound (indexedGet t) (indexedTable_checks t ht)

/-- At canonical keys in degree at most 15, a stored value is a Specht character value. -/
theorem indexedTable_character {n : ℕ} (hn : n ≤ 15) (t : IndexedTable)
    (ht : checkIndexedTable t = true) (i : ℕ) (e : IndexedEntry)
    (he : indexedGet t i = some e) (lam rho : Nat.Partition n)
    (hlam : e.entry.shape = partitionRows lam) (hrho : e.entry.cycles = partitionRows rho) :
    e.entry.value = TauCeti.spechtCharValue lam rho := by
  rw [indexedTable_sound t ht i e he, hlam, hrho]
  exact agreementThrough15 n hn lam rho

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.indexedSum_sound
#print axioms HSTZ.TauCetiFinite.indexedCheck_sound
#print axioms HSTZ.TauCetiFinite.indexedTable_checks
#print axioms HSTZ.TauCetiFinite.indexedTable_sound
#print axioms HSTZ.TauCetiFinite.indexedTable_character
