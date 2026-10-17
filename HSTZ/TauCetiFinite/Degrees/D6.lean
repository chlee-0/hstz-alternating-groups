import HSTZ.TauCetiFinite.IndexedMoments

/-! Finite character-certificate data for degree 6. Every move is regenerated and every
reference checked in Lean; the explicit class lists are proved complete. No external
computation and no compiler-trust axiom is a proof input. -/
namespace HSTZ.TauCetiFinite.D6
open HSTZ.MurnaghanNakayama

def block0 : Array IndexedEntry := #[
  ⟨⟨[],[],(1)⟩,[]⟩,
  ⟨⟨[6],[6],(1)⟩,[0]⟩,
  ⟨⟨[1],[1],(1)⟩,[0]⟩,
  ⟨⟨[6],[5,1],(1)⟩,[2]⟩,
  ⟨⟨[2],[2],(1)⟩,[0]⟩,
  ⟨⟨[6],[4,2],(1)⟩,[4]⟩,
  ⟨⟨[2],[1,1],(1)⟩,[2]⟩,
  ⟨⟨[6],[4,1,1],(1)⟩,[6]⟩,
  ⟨⟨[3],[3],(1)⟩,[0]⟩,
  ⟨⟨[6],[3,3],(1)⟩,[8]⟩,
  ⟨⟨[3],[2,1],(1)⟩,[2]⟩,
  ⟨⟨[6],[3,2,1],(1)⟩,[10]⟩,
  ⟨⟨[3],[1,1,1],(1)⟩,[6]⟩,
  ⟨⟨[6],[3,1,1,1],(1)⟩,[12]⟩,
  ⟨⟨[4],[2,2],(1)⟩,[4]⟩,
  ⟨⟨[6],[2,2,2],(1)⟩,[14]⟩
]

def block1 : Array IndexedEntry := #[
  ⟨⟨[4],[2,1,1],(1)⟩,[6]⟩,
  ⟨⟨[6],[2,2,1,1],(1)⟩,[16]⟩,
  ⟨⟨[4],[1,1,1,1],(1)⟩,[12]⟩,
  ⟨⟨[6],[2,1,1,1,1],(1)⟩,[18]⟩,
  ⟨⟨[5],[1,1,1,1,1],(1)⟩,[18]⟩,
  ⟨⟨[6],[1,1,1,1,1,1],(1)⟩,[20]⟩,
  ⟨⟨[5,1],[6],(-1)⟩,[0]⟩,
  ⟨⟨[5,1],[5,1],(0)⟩,[]⟩,
  ⟨⟨[1,1],[2],(-1)⟩,[0]⟩,
  ⟨⟨[5,1],[4,2],(-1)⟩,[24]⟩,
  ⟨⟨[1,1],[1,1],(1)⟩,[2]⟩,
  ⟨⟨[5,1],[4,1,1],(1)⟩,[26]⟩,
  ⟨⟨[2,1],[3],(-1)⟩,[0]⟩,
  ⟨⟨[5,1],[3,3],(-1)⟩,[28]⟩,
  ⟨⟨[2,1],[2,1],(0)⟩,[]⟩,
  ⟨⟨[5,1],[3,2,1],(0)⟩,[30]⟩
]

def block2 : Array IndexedEntry := #[
  ⟨⟨[2,1],[1,1,1],(2)⟩,[26,6]⟩,
  ⟨⟨[5,1],[3,1,1,1],(2)⟩,[32]⟩,
  ⟨⟨[3,1],[2,2],(-1)⟩,[24]⟩,
  ⟨⟨[5,1],[2,2,2],(-1)⟩,[34]⟩,
  ⟨⟨[3,1],[2,1,1],(1)⟩,[26]⟩,
  ⟨⟨[5,1],[2,2,1,1],(1)⟩,[36]⟩,
  ⟨⟨[3,1],[1,1,1,1],(3)⟩,[32,12]⟩,
  ⟨⟨[5,1],[2,1,1,1,1],(3)⟩,[38]⟩,
  ⟨⟨[4,1],[1,1,1,1,1],(4)⟩,[38,18]⟩,
  ⟨⟨[5,1],[1,1,1,1,1,1],(5)⟩,[40,20]⟩,
  ⟨⟨[4,2],[6],(0)⟩,[]⟩,
  ⟨⟨[4,2],[5,1],(-1)⟩,[2]⟩,
  ⟨⟨[4,2],[4,2],(1)⟩,[24]⟩,
  ⟨⟨[4,2],[4,1,1],(-1)⟩,[26]⟩,
  ⟨⟨[4,2],[3,3],(0)⟩,[]⟩,
  ⟨⟨[4,2],[3,2,1],(0)⟩,[]⟩
]

def block3 : Array IndexedEntry := #[
  ⟨⟨[4,2],[3,1,1,1],(0)⟩,[]⟩,
  ⟨⟨[2,2],[2,2],(2)⟩,[24,4]⟩,
  ⟨⟨[4,2],[2,2,2],(3)⟩,[49,14]⟩,
  ⟨⟨[2,2],[2,1,1],(0)⟩,[26,6]⟩,
  ⟨⟨[4,2],[2,2,1,1],(1)⟩,[51,16]⟩,
  ⟨⟨[2,2],[1,1,1,1],(2)⟩,[32]⟩,
  ⟨⟨[4,2],[2,1,1,1,1],(3)⟩,[53,18]⟩,
  ⟨⟨[3,2],[1,1,1,1,1],(5)⟩,[53,38]⟩,
  ⟨⟨[4,2],[1,1,1,1,1,1],(9)⟩,[55,40]⟩,
  ⟨⟨[4,1,1],[6],(1)⟩,[0]⟩,
  ⟨⟨[4,1,1],[5,1],(0)⟩,[]⟩,
  ⟨⟨[4,1,1],[4,2],(0)⟩,[]⟩,
  ⟨⟨[4,1,1],[4,1,1],(0)⟩,[]⟩,
  ⟨⟨[1,1,1],[3],(1)⟩,[0]⟩,
  ⟨⟨[4,1,1],[3,3],(1)⟩,[61]⟩,
  ⟨⟨[1,1,1],[2,1],(-1)⟩,[2]⟩
]

def block4 : Array IndexedEntry := #[
  ⟨⟨[4,1,1],[3,2,1],(-1)⟩,[63]⟩,
  ⟨⟨[1,1,1],[1,1,1],(1)⟩,[26]⟩,
  ⟨⟨[4,1,1],[3,1,1,1],(1)⟩,[65]⟩,
  ⟨⟨[2,1,1],[2,2],(-1)⟩,[4]⟩,
  ⟨⟨[4,1,1],[2,2,2],(-2)⟩,[67,14]⟩,
  ⟨⟨[2,1,1],[2,1,1],(-1)⟩,[6]⟩,
  ⟨⟨[4,1,1],[2,2,1,1],(-2)⟩,[69,16]⟩,
  ⟨⟨[2,1,1],[1,1,1,1],(3)⟩,[65,32]⟩,
  ⟨⟨[4,1,1],[2,1,1,1,1],(2)⟩,[71,18]⟩,
  ⟨⟨[3,1,1],[1,1,1,1,1],(6)⟩,[71,38]⟩,
  ⟨⟨[4,1,1],[1,1,1,1,1,1],(10)⟩,[73,40]⟩,
  ⟨⟨[3,3],[6],(0)⟩,[]⟩,
  ⟨⟨[3,3],[5,1],(0)⟩,[]⟩,
  ⟨⟨[3,3],[4,2],(-1)⟩,[4]⟩,
  ⟨⟨[3,3],[4,1,1],(-1)⟩,[6]⟩,
  ⟨⟨[3,3],[3,3],(2)⟩,[28,8]⟩
]

def block5 : Array IndexedEntry := #[
  ⟨⟨[3,3],[3,2,1],(1)⟩,[30,10]⟩,
  ⟨⟨[3,3],[3,1,1,1],(-1)⟩,[32,12]⟩,
  ⟨⟨[3,3],[2,2,2],(-3)⟩,[49,34]⟩,
  ⟨⟨[3,3],[2,2,1,1],(1)⟩,[51,36]⟩,
  ⟨⟨[3,3],[2,1,1,1,1],(1)⟩,[53,38]⟩,
  ⟨⟨[3,3],[1,1,1,1,1,1],(5)⟩,[55]⟩,
  ⟨⟨[3,2,1],[6],(0)⟩,[]⟩,
  ⟨⟨[3,2,1],[5,1],(1)⟩,[2]⟩,
  ⟨⟨[3,2,1],[4,2],(0)⟩,[]⟩,
  ⟨⟨[3,2,1],[4,1,1],(0)⟩,[]⟩,
  ⟨⟨[3,2,1],[3,3],(-2)⟩,[61,8]⟩,
  ⟨⟨[3,2,1],[3,2,1],(0)⟩,[63,10]⟩,
  ⟨⟨[3,2,1],[3,1,1,1],(-2)⟩,[65,12]⟩,
  ⟨⟨[3,2,1],[2,2,2],(0)⟩,[]⟩,
  ⟨⟨[3,2,1],[2,2,1,1],(0)⟩,[]⟩,
  ⟨⟨[3,2,1],[2,1,1,1,1],(0)⟩,[]⟩
]

def block6 : Array IndexedEntry := #[
  ⟨⟨[2,2,1],[1,1,1,1,1],(5)⟩,[71,53]⟩,
  ⟨⟨[3,2,1],[1,1,1,1,1,1],(16)⟩,[96,73,55]⟩,
  ⟨⟨[3,1,1,1],[6],(-1)⟩,[0]⟩,
  ⟨⟨[3,1,1,1],[5,1],(0)⟩,[]⟩,
  ⟨⟨[3,1,1,1],[4,2],(0)⟩,[]⟩,
  ⟨⟨[3,1,1,1],[4,1,1],(0)⟩,[]⟩,
  ⟨⟨[3,1,1,1],[3,3],(1)⟩,[8]⟩,
  ⟨⟨[3,1,1,1],[3,2,1],(1)⟩,[10]⟩,
  ⟨⟨[3,1,1,1],[3,1,1,1],(1)⟩,[12]⟩,
  ⟨⟨[1,1,1,1],[2,2],(1)⟩,[24]⟩,
  ⟨⟨[3,1,1,1],[2,2,2],(2)⟩,[105,34]⟩,
  ⟨⟨[1,1,1,1],[2,1,1],(-1)⟩,[26]⟩,
  ⟨⟨[3,1,1,1],[2,2,1,1],(-2)⟩,[107,36]⟩,
  ⟨⟨[1,1,1,1],[1,1,1,1],(1)⟩,[65]⟩,
  ⟨⟨[3,1,1,1],[2,1,1,1,1],(-2)⟩,[109,38]⟩,
  ⟨⟨[2,1,1,1],[1,1,1,1,1],(4)⟩,[109,71]⟩
]

def block7 : Array IndexedEntry := #[
  ⟨⟨[3,1,1,1],[1,1,1,1,1,1],(10)⟩,[111,73]⟩,
  ⟨⟨[2,2,2],[6],(0)⟩,[]⟩,
  ⟨⟨[2,2,2],[5,1],(0)⟩,[]⟩,
  ⟨⟨[2,2,2],[4,2],(-1)⟩,[24]⟩,
  ⟨⟨[2,2,2],[4,1,1],(1)⟩,[26]⟩,
  ⟨⟨[2,2,2],[3,3],(2)⟩,[61,28]⟩,
  ⟨⟨[2,2,2],[3,2,1],(-1)⟩,[63,30]⟩,
  ⟨⟨[2,2,2],[3,1,1,1],(-1)⟩,[65,32]⟩,
  ⟨⟨[2,2,2],[2,2,2],(3)⟩,[67,49]⟩,
  ⟨⟨[2,2,2],[2,2,1,1],(1)⟩,[69,51]⟩,
  ⟨⟨[2,2,2],[2,1,1,1,1],(-1)⟩,[71,53]⟩,
  ⟨⟨[2,2,2],[1,1,1,1,1,1],(5)⟩,[96]⟩,
  ⟨⟨[2,2,1,1],[6],(0)⟩,[]⟩,
  ⟨⟨[2,2,1,1],[5,1],(-1)⟩,[2]⟩,
  ⟨⟨[2,2,1,1],[4,2],(1)⟩,[4]⟩,
  ⟨⟨[2,2,1,1],[4,1,1],(1)⟩,[6]⟩
]

def block8 : Array IndexedEntry := #[
  ⟨⟨[2,2,1,1],[3,3],(0)⟩,[]⟩,
  ⟨⟨[2,2,1,1],[3,2,1],(0)⟩,[]⟩,
  ⟨⟨[2,2,1,1],[3,1,1,1],(0)⟩,[]⟩,
  ⟨⟨[2,2,1,1],[2,2,2],(-3)⟩,[105,49]⟩,
  ⟨⟨[2,2,1,1],[2,2,1,1],(1)⟩,[107,51]⟩,
  ⟨⟨[2,2,1,1],[2,1,1,1,1],(-3)⟩,[109,53]⟩,
  ⟨⟨[2,2,1,1],[1,1,1,1,1,1],(9)⟩,[111,96]⟩,
  ⟨⟨[2,1,1,1,1],[6],(1)⟩,[0]⟩,
  ⟨⟨[2,1,1,1,1],[5,1],(0)⟩,[]⟩,
  ⟨⟨[2,1,1,1,1],[4,2],(-1)⟩,[4]⟩,
  ⟨⟨[2,1,1,1,1],[4,1,1],(-1)⟩,[6]⟩,
  ⟨⟨[2,1,1,1,1],[3,3],(-1)⟩,[28]⟩,
  ⟨⟨[2,1,1,1,1],[3,2,1],(0)⟩,[30]⟩,
  ⟨⟨[2,1,1,1,1],[3,1,1,1],(2)⟩,[32]⟩,
  ⟨⟨[2,1,1,1,1],[2,2,2],(1)⟩,[67]⟩,
  ⟨⟨[2,1,1,1,1],[2,2,1,1],(1)⟩,[69]⟩
]

def block9 : Array IndexedEntry := #[
  ⟨⟨[2,1,1,1,1],[2,1,1,1,1],(-3)⟩,[71]⟩,
  ⟨⟨[1,1,1,1,1],[1,1,1,1,1],(1)⟩,[109]⟩,
  ⟨⟨[2,1,1,1,1],[1,1,1,1,1,1],(5)⟩,[145,111]⟩,
  ⟨⟨[1,1,1,1,1,1],[6],(-1)⟩,[0]⟩,
  ⟨⟨[1,1,1,1,1,1],[5,1],(1)⟩,[2]⟩,
  ⟨⟨[1,1,1,1,1,1],[4,2],(1)⟩,[24]⟩,
  ⟨⟨[1,1,1,1,1,1],[4,1,1],(-1)⟩,[26]⟩,
  ⟨⟨[1,1,1,1,1,1],[3,3],(1)⟩,[61]⟩,
  ⟨⟨[1,1,1,1,1,1],[3,2,1],(-1)⟩,[63]⟩,
  ⟨⟨[1,1,1,1,1,1],[3,1,1,1],(1)⟩,[65]⟩,
  ⟨⟨[1,1,1,1,1,1],[2,2,2],(-1)⟩,[105]⟩,
  ⟨⟨[1,1,1,1,1,1],[2,2,1,1],(1)⟩,[107]⟩,
  ⟨⟨[1,1,1,1,1,1],[2,1,1,1,1],(-1)⟩,[109]⟩,
  ⟨⟨[1,1,1,1,1,1],[1,1,1,1,1,1],(1)⟩,[145]⟩
]

def blockGroup0 : ℕ → Array IndexedEntry
  | 0 => block0
  | 1 => block1
  | 2 => block2
  | 3 => block3
  | 4 => block4
  | 5 => block5
  | 6 => block6
  | 7 => block7
  | 8 => block8
  | 9 => block9
  | _ => #[]

def superGroup0 (k : ℕ) : Array IndexedEntry :=
  match (k/16)%16 with
  | 0 => blockGroup0 (k%16)
  | _ => #[]

def table : IndexedTable := ⟨158, fun k =>
  match k/256 with
  | 0 => superGroup0 k
  | _ => #[]⟩

theorem group0_checked : checkIndexedGroup table 0 = true := by decide

theorem table_checked : checkIndexedTable table = true := by
  unfold checkIndexedTable
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 1 := by simpa [table] using List.mem_range.mp hk
  interval_cases k
  · exact group0_checked

def classes : List Shape := [[6],[5,1],[4,2],[4,1,1],[3,3],[3,2,1],[3,1,1,1],[2,2,2],[2,2,1,1],[2,1,1,1,1],[1,1,1,1,1,1]]
theorem classes_checked : checkClasses 6 classes = true := by decide

def refs0 : List ℕ := [1,3,5,7,9,11,13,15,17,19,21]
def refs1 : List ℕ := [22,23,25,27,29,31,33,35,37,39,41]
def refs2 : List ℕ := [42,43,44,45,46,47,48,50,52,54,56]
def refs3 : List ℕ := [57,58,59,60,62,64,66,68,70,72,74]
def refs4 : List ℕ := [75,76,77,78,79,80,81,82,83,84,85]
def refs5 : List ℕ := [86,87,88,89,90,91,92,93,94,95,97]
def refs6 : List ℕ := [98,99,100,101,102,103,104,106,108,110,112]
def refs7 : List ℕ := [113,114,115,116,117,118,119,120,121,122,123]
def refs8 : List ℕ := [124,125,126,127,128,129,130,131,132,133,134]
def refs9 : List ℕ := [135,136,137,138,139,140,141,142,143,144,146]
def refs10 : List ℕ := [147,148,149,150,151,152,153,154,155,156,157]
theorem row0_checked : checkIndexedRow table [6] classes refs0 = true := by decide
theorem residue0_checked : (2 * indexedCoverSum table 6 classes refs2 refs0) % 1000000007 ≠ 0 := by decide

theorem row1_checked : checkIndexedRow table [5,1] classes refs1 = true := by decide
theorem residue1_checked : (2 * indexedCoverSum table 6 classes refs2 refs1) % 1000000007 ≠ 0 := by decide

theorem row2_checked : checkIndexedRow table [4,2] classes refs2 = true := by decide
theorem residue2_checked : (2 * indexedCoverSum table 6 classes refs2 refs2) % 1000000007 ≠ 0 := by decide

theorem row3_checked : checkIndexedRow table [4,1,1] classes refs3 = true := by decide
theorem residue3_checked : (2 * indexedCoverSum table 6 classes refs2 refs3) % 1000000007 ≠ 0 := by decide

theorem row4_checked : checkIndexedRow table [3,3] classes refs4 = true := by decide
theorem residue4_checked : (2 * indexedCoverSum table 6 classes refs2 refs4) % 1000000007 ≠ 0 := by decide

theorem row5_checked : checkIndexedRow table [3,2,1] classes refs5 = true := by decide
theorem residue5_checked : (2 * indexedCoverSum table 6 classes refs2 refs5) % 1000000007 ≠ 0 := by decide

theorem row6_checked : checkIndexedRow table [3,1,1,1] classes refs6 = true := by decide
theorem residue6_checked : (2 * indexedCoverSum table 6 classes refs2 refs6) % 1000000007 ≠ 0 := by decide

theorem row7_checked : checkIndexedRow table [2,2,2] classes refs7 = true := by decide
theorem residue7_checked : (2 * indexedCoverSum table 6 classes refs2 refs7) % 1000000007 ≠ 0 := by decide

theorem row8_checked : checkIndexedRow table [2,2,1,1] classes refs8 = true := by decide
theorem residue8_checked : (2 * indexedCoverSum table 6 classes refs2 refs8) % 1000000007 ≠ 0 := by decide

theorem row9_checked : checkIndexedRow table [2,1,1,1,1] classes refs9 = true := by decide
theorem residue9_checked : (2 * indexedCoverSum table 6 classes refs2 refs9) % 1000000007 ≠ 0 := by decide

theorem row10_checked : checkIndexedRow table [1,1,1,1,1,1] classes refs10 = true := by decide
theorem residue10_checked : (2 * indexedCoverSum table 6 classes refs2 refs10) % 1000000007 ≠ 0 := by decide

theorem norm_checked : 2 * indexedNormSum table 6 classes refs2 = ((6 : ℕ).factorial : ℤ) := by decide

theorem targets_checked : ∀ nu ∈ classes, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 6 classes refs2 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classes, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs0, row0_checked, residue0_checked⟩
  · exact ⟨refs1, row1_checked, residue1_checked⟩
  · exact ⟨refs2, row2_checked, residue2_checked⟩
  · exact ⟨refs3, row3_checked, residue3_checked⟩
  · exact ⟨refs4, row4_checked, residue4_checked⟩
  · exact ⟨refs5, row5_checked, residue5_checked⟩
  · exact ⟨refs6, row6_checked, residue6_checked⟩
  · exact ⟨refs7, row7_checked, residue7_checked⟩
  · exact ⟨refs8, row8_checked, residue8_checked⟩
  · exact ⟨refs9, row9_checked, residue9_checked⟩
  · exact ⟨refs10, row10_checked, residue10_checked⟩

def witness : Nat.Partition 6 where
  parts := [4,2]
  parts_pos := by decide
  parts_sum := rfl

theorem witness_rows : partitionRows witness = [4,2] := by
  change ([4,2] : Multiset ℕ).sort (· ≥ ·) = [4,2]
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (by simp)

theorem norm : evenNormNumerator witness = ((6 : ℕ).factorial : ℤ) := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs2 = true := by
    rw [witness_rows]; exact row2_checked
  rw [← indexedNorm_eq_evenNorm (by decide) table table_checked classes classes_checked witness refs2 hr]
  exact norm_checked

theorem cover_residue (nu : Nat.Partition 6) :
    evenCoverNumerator witness nu % 1000000007 ≠ 0 := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs2 = true := by
    rw [witness_rows]; exact row2_checked
  obtain ⟨refs, hp, he⟩ := targets_checked (partitionRows nu)
    (checkClasses_complete classes classes_checked nu)
  rw [← indexedCover_eq_evenCover (by decide) table table_checked classes classes_checked witness nu refs2 refs hr hp]
  exact he

end HSTZ.TauCetiFinite.D6
#print axioms HSTZ.TauCetiFinite.D6.table_checked
#print axioms HSTZ.TauCetiFinite.D6.classes_checked
#print axioms HSTZ.TauCetiFinite.D6.norm_checked
#print axioms HSTZ.TauCetiFinite.D6.targets_checked
#print axioms HSTZ.TauCetiFinite.D6.norm
#print axioms HSTZ.TauCetiFinite.D6.cover_residue
