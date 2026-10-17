import HSTZ.TauCetiFinite.IndexedMoments

/-! Finite character-certificate data for degree 7. Every move is regenerated and every
reference checked in Lean; the explicit class lists are proved complete. No external
computation and no compiler-trust axiom is a proof input. -/
namespace HSTZ.TauCetiFinite.D7
open HSTZ.MurnaghanNakayama

def block0 : Array IndexedEntry := #[
  ⟨⟨[],[],(1)⟩,[]⟩,
  ⟨⟨[7],[7],(1)⟩,[0]⟩,
  ⟨⟨[1],[1],(1)⟩,[0]⟩,
  ⟨⟨[7],[6,1],(1)⟩,[2]⟩,
  ⟨⟨[2],[2],(1)⟩,[0]⟩,
  ⟨⟨[7],[5,2],(1)⟩,[4]⟩,
  ⟨⟨[2],[1,1],(1)⟩,[2]⟩,
  ⟨⟨[7],[5,1,1],(1)⟩,[6]⟩,
  ⟨⟨[3],[3],(1)⟩,[0]⟩,
  ⟨⟨[7],[4,3],(1)⟩,[8]⟩,
  ⟨⟨[3],[2,1],(1)⟩,[2]⟩,
  ⟨⟨[7],[4,2,1],(1)⟩,[10]⟩,
  ⟨⟨[3],[1,1,1],(1)⟩,[6]⟩,
  ⟨⟨[7],[4,1,1,1],(1)⟩,[12]⟩,
  ⟨⟨[4],[3,1],(1)⟩,[2]⟩,
  ⟨⟨[7],[3,3,1],(1)⟩,[14]⟩
]

def block1 : Array IndexedEntry := #[
  ⟨⟨[4],[2,2],(1)⟩,[4]⟩,
  ⟨⟨[7],[3,2,2],(1)⟩,[16]⟩,
  ⟨⟨[4],[2,1,1],(1)⟩,[6]⟩,
  ⟨⟨[7],[3,2,1,1],(1)⟩,[18]⟩,
  ⟨⟨[4],[1,1,1,1],(1)⟩,[12]⟩,
  ⟨⟨[7],[3,1,1,1,1],(1)⟩,[20]⟩,
  ⟨⟨[5],[2,2,1],(1)⟩,[10]⟩,
  ⟨⟨[7],[2,2,2,1],(1)⟩,[22]⟩,
  ⟨⟨[5],[2,1,1,1],(1)⟩,[12]⟩,
  ⟨⟨[7],[2,2,1,1,1],(1)⟩,[24]⟩,
  ⟨⟨[5],[1,1,1,1,1],(1)⟩,[20]⟩,
  ⟨⟨[7],[2,1,1,1,1,1],(1)⟩,[26]⟩,
  ⟨⟨[6],[1,1,1,1,1,1],(1)⟩,[26]⟩,
  ⟨⟨[7],[1,1,1,1,1,1,1],(1)⟩,[28]⟩,
  ⟨⟨[6,1],[7],(-1)⟩,[0]⟩,
  ⟨⟨[6,1],[6,1],(0)⟩,[]⟩
]

def block2 : Array IndexedEntry := #[
  ⟨⟨[1,1],[2],(-1)⟩,[0]⟩,
  ⟨⟨[6,1],[5,2],(-1)⟩,[32]⟩,
  ⟨⟨[1,1],[1,1],(1)⟩,[2]⟩,
  ⟨⟨[6,1],[5,1,1],(1)⟩,[34]⟩,
  ⟨⟨[2,1],[3],(-1)⟩,[0]⟩,
  ⟨⟨[6,1],[4,3],(-1)⟩,[36]⟩,
  ⟨⟨[2,1],[2,1],(0)⟩,[]⟩,
  ⟨⟨[6,1],[4,2,1],(0)⟩,[38]⟩,
  ⟨⟨[2,1],[1,1,1],(2)⟩,[34,6]⟩,
  ⟨⟨[6,1],[4,1,1,1],(2)⟩,[40]⟩,
  ⟨⟨[3,1],[3,1],(0)⟩,[]⟩,
  ⟨⟨[6,1],[3,3,1],(0)⟩,[42]⟩,
  ⟨⟨[3,1],[2,2],(-1)⟩,[32]⟩,
  ⟨⟨[6,1],[3,2,2],(-1)⟩,[44]⟩,
  ⟨⟨[3,1],[2,1,1],(1)⟩,[34]⟩,
  ⟨⟨[6,1],[3,2,1,1],(1)⟩,[46]⟩
]

def block3 : Array IndexedEntry := #[
  ⟨⟨[3,1],[1,1,1,1],(3)⟩,[40,12]⟩,
  ⟨⟨[6,1],[3,1,1,1,1],(3)⟩,[48]⟩,
  ⟨⟨[4,1],[2,2,1],(0)⟩,[38]⟩,
  ⟨⟨[6,1],[2,2,2,1],(0)⟩,[50]⟩,
  ⟨⟨[4,1],[2,1,1,1],(2)⟩,[40]⟩,
  ⟨⟨[6,1],[2,2,1,1,1],(2)⟩,[52]⟩,
  ⟨⟨[4,1],[1,1,1,1,1],(4)⟩,[48,20]⟩,
  ⟨⟨[6,1],[2,1,1,1,1,1],(4)⟩,[54]⟩,
  ⟨⟨[5,1],[1,1,1,1,1,1],(5)⟩,[54,26]⟩,
  ⟨⟨[6,1],[1,1,1,1,1,1,1],(6)⟩,[56,28]⟩,
  ⟨⟨[5,2],[7],(0)⟩,[]⟩,
  ⟨⟨[5,2],[6,1],(-1)⟩,[2]⟩,
  ⟨⟨[5,2],[5,2],(1)⟩,[32]⟩,
  ⟨⟨[5,2],[5,1,1],(-1)⟩,[34]⟩,
  ⟨⟨[5,2],[4,3],(0)⟩,[]⟩,
  ⟨⟨[5,2],[4,2,1],(0)⟩,[]⟩
]

def block4 : Array IndexedEntry := #[
  ⟨⟨[5,2],[4,1,1,1],(0)⟩,[]⟩,
  ⟨⟨[2,2],[3,1],(-1)⟩,[2]⟩,
  ⟨⟨[5,2],[3,3,1],(-1)⟩,[65]⟩,
  ⟨⟨[2,2],[2,2],(2)⟩,[32,4]⟩,
  ⟨⟨[5,2],[3,2,2],(2)⟩,[67]⟩,
  ⟨⟨[2,2],[2,1,1],(0)⟩,[34,6]⟩,
  ⟨⟨[5,2],[3,2,1,1],(0)⟩,[69]⟩,
  ⟨⟨[2,2],[1,1,1,1],(2)⟩,[40]⟩,
  ⟨⟨[5,2],[3,1,1,1,1],(2)⟩,[71]⟩,
  ⟨⟨[3,2],[2,2,1],(1)⟩,[10]⟩,
  ⟨⟨[5,2],[2,2,2,1],(2)⟩,[73,22]⟩,
  ⟨⟨[3,2],[2,1,1,1],(1)⟩,[12]⟩,
  ⟨⟨[5,2],[2,2,1,1,1],(2)⟩,[75,24]⟩,
  ⟨⟨[3,2],[1,1,1,1,1],(5)⟩,[71,48]⟩,
  ⟨⟨[5,2],[2,1,1,1,1,1],(6)⟩,[77,26]⟩,
  ⟨⟨[4,2],[1,1,1,1,1,1],(9)⟩,[77,54]⟩
]

def block5 : Array IndexedEntry := #[
  ⟨⟨[5,2],[1,1,1,1,1,1,1],(14)⟩,[79,56]⟩,
  ⟨⟨[5,1,1],[7],(1)⟩,[0]⟩,
  ⟨⟨[5,1,1],[6,1],(0)⟩,[]⟩,
  ⟨⟨[5,1,1],[5,2],(0)⟩,[]⟩,
  ⟨⟨[5,1,1],[5,1,1],(0)⟩,[]⟩,
  ⟨⟨[1,1,1],[3],(1)⟩,[0]⟩,
  ⟨⟨[5,1,1],[4,3],(1)⟩,[85]⟩,
  ⟨⟨[1,1,1],[2,1],(-1)⟩,[2]⟩,
  ⟨⟨[5,1,1],[4,2,1],(-1)⟩,[87]⟩,
  ⟨⟨[1,1,1],[1,1,1],(1)⟩,[34]⟩,
  ⟨⟨[5,1,1],[4,1,1,1],(1)⟩,[89]⟩,
  ⟨⟨[2,1,1],[3,1],(0)⟩,[]⟩,
  ⟨⟨[5,1,1],[3,3,1],(0)⟩,[91]⟩,
  ⟨⟨[2,1,1],[2,2],(-1)⟩,[4]⟩,
  ⟨⟨[5,1,1],[3,2,2],(-1)⟩,[93]⟩,
  ⟨⟨[2,1,1],[2,1,1],(-1)⟩,[6]⟩
]

def block6 : Array IndexedEntry := #[
  ⟨⟨[5,1,1],[3,2,1,1],(-1)⟩,[95]⟩,
  ⟨⟨[2,1,1],[1,1,1,1],(3)⟩,[89,40]⟩,
  ⟨⟨[5,1,1],[3,1,1,1,1],(3)⟩,[97]⟩,
  ⟨⟨[3,1,1],[2,2,1],(-2)⟩,[87,10]⟩,
  ⟨⟨[5,1,1],[2,2,2,1],(-3)⟩,[99,22]⟩,
  ⟨⟨[3,1,1],[2,1,1,1],(0)⟩,[89,12]⟩,
  ⟨⟨[5,1,1],[2,2,1,1,1],(-1)⟩,[101,24]⟩,
  ⟨⟨[3,1,1],[1,1,1,1,1],(6)⟩,[97,48]⟩,
  ⟨⟨[5,1,1],[2,1,1,1,1,1],(5)⟩,[103,26]⟩,
  ⟨⟨[4,1,1],[1,1,1,1,1,1],(10)⟩,[103,54]⟩,
  ⟨⟨[5,1,1],[1,1,1,1,1,1,1],(15)⟩,[105,56]⟩,
  ⟨⟨[4,3],[7],(0)⟩,[]⟩,
  ⟨⟨[4,3],[6,1],(0)⟩,[]⟩,
  ⟨⟨[4,3],[5,2],(-1)⟩,[4]⟩,
  ⟨⟨[4,3],[5,1,1],(-1)⟩,[6]⟩,
  ⟨⟨[4,3],[4,3],(1)⟩,[36]⟩
]

def block7 : Array IndexedEntry := #[
  ⟨⟨[4,3],[4,2,1],(0)⟩,[38]⟩,
  ⟨⟨[4,3],[4,1,1,1],(-2)⟩,[40]⟩,
  ⟨⟨[4,3],[3,3,1],(2)⟩,[65,14]⟩,
  ⟨⟨[4,3],[3,2,2],(-1)⟩,[67,16]⟩,
  ⟨⟨[4,3],[3,2,1,1],(1)⟩,[69,18]⟩,
  ⟨⟨[4,3],[3,1,1,1,1],(-1)⟩,[71,20]⟩,
  ⟨⟨[4,3],[2,2,2,1],(0)⟩,[50]⟩,
  ⟨⟨[4,3],[2,2,1,1,1],(2)⟩,[52]⟩,
  ⟨⟨[4,3],[2,1,1,1,1,1],(4)⟩,[54]⟩,
  ⟨⟨[3,3],[1,1,1,1,1,1],(5)⟩,[77]⟩,
  ⟨⟨[4,3],[1,1,1,1,1,1,1],(14)⟩,[121,79]⟩,
  ⟨⟨[4,2,1],[7],(0)⟩,[]⟩,
  ⟨⟨[4,2,1],[6,1],(1)⟩,[2]⟩,
  ⟨⟨[4,2,1],[5,2],(0)⟩,[]⟩,
  ⟨⟨[4,2,1],[5,1,1],(0)⟩,[]⟩,
  ⟨⟨[4,2,1],[4,3],(-1)⟩,[85]⟩
]

def block8 : Array IndexedEntry := #[
  ⟨⟨[4,2,1],[4,2,1],(1)⟩,[87]⟩,
  ⟨⟨[4,2,1],[4,1,1,1],(-1)⟩,[89]⟩,
  ⟨⟨[4,2,1],[3,3,1],(-1)⟩,[14]⟩,
  ⟨⟨[4,2,1],[3,2,2],(-1)⟩,[16]⟩,
  ⟨⟨[4,2,1],[3,2,1,1],(-1)⟩,[18]⟩,
  ⟨⟨[4,2,1],[3,1,1,1,1],(-1)⟩,[20]⟩,
  ⟨⟨[2,2,1],[2,2,1],(1)⟩,[87]⟩,
  ⟨⟨[4,2,1],[2,2,2,1],(1)⟩,[134]⟩,
  ⟨⟨[2,2,1],[2,1,1,1],(-1)⟩,[89]⟩,
  ⟨⟨[4,2,1],[2,2,1,1,1],(-1)⟩,[136]⟩,
  ⟨⟨[2,2,1],[1,1,1,1,1],(5)⟩,[97,71]⟩,
  ⟨⟨[4,2,1],[2,1,1,1,1,1],(5)⟩,[138]⟩,
  ⟨⟨[3,2,1],[1,1,1,1,1,1],(16)⟩,[138,103,77]⟩,
  ⟨⟨[4,2,1],[1,1,1,1,1,1,1],(35)⟩,[140,105,79]⟩,
  ⟨⟨[4,1,1,1],[7],(-1)⟩,[0]⟩,
  ⟨⟨[4,1,1,1],[6,1],(0)⟩,[]⟩
]

def block9 : Array IndexedEntry := #[
  ⟨⟨[4,1,1,1],[5,2],(0)⟩,[]⟩,
  ⟨⟨[4,1,1,1],[5,1,1],(0)⟩,[]⟩,
  ⟨⟨[4,1,1,1],[4,3],(0)⟩,[]⟩,
  ⟨⟨[4,1,1,1],[4,2,1],(0)⟩,[]⟩,
  ⟨⟨[4,1,1,1],[4,1,1,1],(0)⟩,[]⟩,
  ⟨⟨[1,1,1,1],[3,1],(1)⟩,[2]⟩,
  ⟨⟨[4,1,1,1],[3,3,1],(2)⟩,[149,14]⟩,
  ⟨⟨[1,1,1,1],[2,2],(1)⟩,[32]⟩,
  ⟨⟨[4,1,1,1],[3,2,2],(2)⟩,[151,16]⟩,
  ⟨⟨[1,1,1,1],[2,1,1],(-1)⟩,[34]⟩,
  ⟨⟨[4,1,1,1],[3,2,1,1],(0)⟩,[153,18]⟩,
  ⟨⟨[1,1,1,1],[1,1,1,1],(1)⟩,[89]⟩,
  ⟨⟨[4,1,1,1],[3,1,1,1,1],(2)⟩,[155,20]⟩,
  ⟨⟨[2,1,1,1],[2,2,1],(0)⟩,[38]⟩,
  ⟨⟨[4,1,1,1],[2,2,2,1],(0)⟩,[157,50]⟩,
  ⟨⟨[2,1,1,1],[2,1,1,1],(-2)⟩,[40]⟩
]

def block10 : Array IndexedEntry := #[
  ⟨⟨[4,1,1,1],[2,2,1,1,1],(-4)⟩,[159,52]⟩,
  ⟨⟨[2,1,1,1],[1,1,1,1,1],(4)⟩,[155,97]⟩,
  ⟨⟨[4,1,1,1],[2,1,1,1,1,1],(0)⟩,[161,54]⟩,
  ⟨⟨[3,1,1,1],[1,1,1,1,1,1],(10)⟩,[161,103]⟩,
  ⟨⟨[4,1,1,1],[1,1,1,1,1,1,1],(20)⟩,[163,105]⟩,
  ⟨⟨[3,3,1],[7],(0)⟩,[]⟩,
  ⟨⟨[3,3,1],[6,1],(0)⟩,[]⟩,
  ⟨⟨[3,3,1],[5,2],(1)⟩,[4]⟩,
  ⟨⟨[3,3,1],[5,1,1],(1)⟩,[6]⟩,
  ⟨⟨[3,3,1],[4,3],(-1)⟩,[8]⟩,
  ⟨⟨[3,3,1],[4,2,1],(-1)⟩,[10]⟩,
  ⟨⟨[3,3,1],[4,1,1,1],(-1)⟩,[12]⟩,
  ⟨⟨[3,3,1],[3,3,1],(0)⟩,[91]⟩,
  ⟨⟨[3,3,1],[3,2,2],(1)⟩,[93]⟩,
  ⟨⟨[3,3,1],[3,2,1,1],(1)⟩,[95]⟩,
  ⟨⟨[3,3,1],[3,1,1,1,1],(-3)⟩,[97]⟩
]

def block11 : Array IndexedEntry := #[
  ⟨⟨[3,3,1],[2,2,2,1],(-3)⟩,[134,99]⟩,
  ⟨⟨[3,3,1],[2,2,1,1,1],(1)⟩,[136,101]⟩,
  ⟨⟨[3,3,1],[2,1,1,1,1,1],(1)⟩,[138,103]⟩,
  ⟨⟨[3,3,1],[1,1,1,1,1,1,1],(21)⟩,[140,121]⟩,
  ⟨⟨[3,2,2],[7],(0)⟩,[]⟩,
  ⟨⟨[3,2,2],[6,1],(0)⟩,[]⟩,
  ⟨⟨[3,2,2],[5,2],(-1)⟩,[32]⟩,
  ⟨⟨[3,2,2],[5,1,1],(1)⟩,[34]⟩,
  ⟨⟨[3,2,2],[4,3],(1)⟩,[85]⟩,
  ⟨⟨[3,2,2],[4,2,1],(-1)⟩,[87]⟩,
  ⟨⟨[3,2,2],[4,1,1,1],(1)⟩,[89]⟩,
  ⟨⟨[3,2,2],[3,3,1],(0)⟩,[42]⟩,
  ⟨⟨[3,2,2],[3,2,2],(1)⟩,[44]⟩,
  ⟨⟨[3,2,2],[3,2,1,1],(-1)⟩,[46]⟩,
  ⟨⟨[3,2,2],[3,1,1,1,1],(-3)⟩,[48]⟩,
  ⟨⟨[3,2,2],[2,2,2,1],(3)⟩,[99,73]⟩
]

def block12 : Array IndexedEntry := #[
  ⟨⟨[3,2,2],[2,2,1,1,1],(1)⟩,[101,75]⟩,
  ⟨⟨[3,2,2],[2,1,1,1,1,1],(-1)⟩,[103,77]⟩,
  ⟨⟨[2,2,2],[1,1,1,1,1,1],(5)⟩,[138]⟩,
  ⟨⟨[3,2,2],[1,1,1,1,1,1,1],(21)⟩,[194,140]⟩,
  ⟨⟨[3,2,1,1],[7],(0)⟩,[]⟩,
  ⟨⟨[3,2,1,1],[6,1],(-1)⟩,[2]⟩,
  ⟨⟨[3,2,1,1],[5,2],(0)⟩,[]⟩,
  ⟨⟨[3,2,1,1],[5,1,1],(0)⟩,[]⟩,
  ⟨⟨[3,2,1,1],[4,3],(1)⟩,[8]⟩,
  ⟨⟨[3,2,1,1],[4,2,1],(1)⟩,[10]⟩,
  ⟨⟨[3,2,1,1],[4,1,1,1],(1)⟩,[12]⟩,
  ⟨⟨[3,2,1,1],[3,3,1],(-1)⟩,[149]⟩,
  ⟨⟨[3,2,1,1],[3,2,2],(-1)⟩,[151]⟩,
  ⟨⟨[3,2,1,1],[3,2,1,1],(1)⟩,[153]⟩,
  ⟨⟨[3,2,1,1],[3,1,1,1,1],(-1)⟩,[155]⟩,
  ⟨⟨[3,2,1,1],[2,2,2,1],(-1)⟩,[73]⟩
]

def block13 : Array IndexedEntry := #[
  ⟨⟨[3,2,1,1],[2,2,1,1,1],(-1)⟩,[75]⟩,
  ⟨⟨[3,2,1,1],[2,1,1,1,1,1],(-5)⟩,[77]⟩,
  ⟨⟨[2,2,1,1],[1,1,1,1,1,1],(9)⟩,[161,138]⟩,
  ⟨⟨[3,2,1,1],[1,1,1,1,1,1,1],(35)⟩,[210,163,140]⟩,
  ⟨⟨[3,1,1,1,1],[7],(1)⟩,[0]⟩,
  ⟨⟨[3,1,1,1,1],[6,1],(0)⟩,[]⟩,
  ⟨⟨[3,1,1,1,1],[5,2],(0)⟩,[]⟩,
  ⟨⟨[3,1,1,1,1],[5,1,1],(0)⟩,[]⟩,
  ⟨⟨[3,1,1,1,1],[4,3],(-1)⟩,[8]⟩,
  ⟨⟨[3,1,1,1,1],[4,2,1],(-1)⟩,[10]⟩,
  ⟨⟨[3,1,1,1,1],[4,1,1,1],(-1)⟩,[12]⟩,
  ⟨⟨[3,1,1,1,1],[3,3,1],(0)⟩,[42]⟩,
  ⟨⟨[3,1,1,1,1],[3,2,2],(-1)⟩,[44]⟩,
  ⟨⟨[3,1,1,1,1],[3,2,1,1],(1)⟩,[46]⟩,
  ⟨⟨[3,1,1,1,1],[3,1,1,1,1],(3)⟩,[48]⟩,
  ⟨⟨[1,1,1,1,1],[2,2,1],(1)⟩,[87]⟩
]

def block14 : Array IndexedEntry := #[
  ⟨⟨[3,1,1,1,1],[2,2,2,1],(3)⟩,[223,99]⟩,
  ⟨⟨[1,1,1,1,1],[2,1,1,1],(-1)⟩,[89]⟩,
  ⟨⟨[3,1,1,1,1],[2,2,1,1,1],(-1)⟩,[225,101]⟩,
  ⟨⟨[1,1,1,1,1],[1,1,1,1,1],(1)⟩,[155]⟩,
  ⟨⟨[3,1,1,1,1],[2,1,1,1,1,1],(-5)⟩,[227,103]⟩,
  ⟨⟨[2,1,1,1,1],[1,1,1,1,1,1],(5)⟩,[227,161]⟩,
  ⟨⟨[3,1,1,1,1],[1,1,1,1,1,1,1],(15)⟩,[229,163]⟩,
  ⟨⟨[2,2,2,1],[7],(0)⟩,[]⟩,
  ⟨⟨[2,2,2,1],[6,1],(0)⟩,[]⟩,
  ⟨⟨[2,2,2,1],[5,2],(1)⟩,[32]⟩,
  ⟨⟨[2,2,2,1],[5,1,1],(-1)⟩,[34]⟩,
  ⟨⟨[2,2,2,1],[4,3],(-1)⟩,[36]⟩,
  ⟨⟨[2,2,2,1],[4,2,1],(0)⟩,[38]⟩,
  ⟨⟨[2,2,2,1],[4,1,1,1],(2)⟩,[40]⟩,
  ⟨⟨[2,2,2,1],[3,3,1],(2)⟩,[149,65]⟩,
  ⟨⟨[2,2,2,1],[3,2,2],(-1)⟩,[151,67]⟩
]

def block15 : Array IndexedEntry := #[
  ⟨⟨[2,2,2,1],[3,2,1,1],(-1)⟩,[153,69]⟩,
  ⟨⟨[2,2,2,1],[3,1,1,1,1],(-1)⟩,[155,71]⟩,
  ⟨⟨[2,2,2,1],[2,2,2,1],(0)⟩,[157]⟩,
  ⟨⟨[2,2,2,1],[2,2,1,1,1],(2)⟩,[159]⟩,
  ⟨⟨[2,2,2,1],[2,1,1,1,1,1],(-4)⟩,[161]⟩,
  ⟨⟨[2,2,2,1],[1,1,1,1,1,1,1],(14)⟩,[210,194]⟩,
  ⟨⟨[2,2,1,1,1],[7],(0)⟩,[]⟩,
  ⟨⟨[2,2,1,1,1],[6,1],(1)⟩,[2]⟩,
  ⟨⟨[2,2,1,1,1],[5,2],(-1)⟩,[4]⟩,
  ⟨⟨[2,2,1,1,1],[5,1,1],(-1)⟩,[6]⟩,
  ⟨⟨[2,2,1,1,1],[4,3],(0)⟩,[]⟩,
  ⟨⟨[2,2,1,1,1],[4,2,1],(0)⟩,[]⟩,
  ⟨⟨[2,2,1,1,1],[4,1,1,1],(0)⟩,[]⟩,
  ⟨⟨[2,2,1,1,1],[3,3,1],(-1)⟩,[65]⟩,
  ⟨⟨[2,2,1,1,1],[3,2,2],(2)⟩,[67]⟩,
  ⟨⟨[2,2,1,1,1],[3,2,1,1],(0)⟩,[69]⟩
]

def block16 : Array IndexedEntry := #[
  ⟨⟨[2,2,1,1,1],[3,1,1,1,1],(2)⟩,[71]⟩,
  ⟨⟨[2,2,1,1,1],[2,2,2,1],(-2)⟩,[223,134]⟩,
  ⟨⟨[2,2,1,1,1],[2,2,1,1,1],(2)⟩,[225,136]⟩,
  ⟨⟨[2,2,1,1,1],[2,1,1,1,1,1],(-6)⟩,[227,138]⟩,
  ⟨⟨[2,2,1,1,1],[1,1,1,1,1,1,1],(14)⟩,[229,210]⟩,
  ⟨⟨[2,1,1,1,1,1],[7],(-1)⟩,[0]⟩,
  ⟨⟨[2,1,1,1,1,1],[6,1],(0)⟩,[]⟩,
  ⟨⟨[2,1,1,1,1,1],[5,2],(1)⟩,[4]⟩,
  ⟨⟨[2,1,1,1,1,1],[5,1,1],(1)⟩,[6]⟩,
  ⟨⟨[2,1,1,1,1,1],[4,3],(1)⟩,[36]⟩,
  ⟨⟨[2,1,1,1,1,1],[4,2,1],(0)⟩,[38]⟩,
  ⟨⟨[2,1,1,1,1,1],[4,1,1,1],(-2)⟩,[40]⟩,
  ⟨⟨[2,1,1,1,1,1],[3,3,1],(0)⟩,[91]⟩,
  ⟨⟨[2,1,1,1,1,1],[3,2,2],(-1)⟩,[93]⟩,
  ⟨⟨[2,1,1,1,1,1],[3,2,1,1],(-1)⟩,[95]⟩,
  ⟨⟨[2,1,1,1,1,1],[3,1,1,1,1],(3)⟩,[97]⟩
]

def block17 : Array IndexedEntry := #[
  ⟨⟨[2,1,1,1,1,1],[2,2,2,1],(0)⟩,[157]⟩,
  ⟨⟨[2,1,1,1,1,1],[2,2,1,1,1],(2)⟩,[159]⟩,
  ⟨⟨[2,1,1,1,1,1],[2,1,1,1,1,1],(-4)⟩,[161]⟩,
  ⟨⟨[1,1,1,1,1,1],[1,1,1,1,1,1],(1)⟩,[227]⟩,
  ⟨⟨[2,1,1,1,1,1],[1,1,1,1,1,1,1],(6)⟩,[275,229]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[7],(1)⟩,[0]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[6,1],(-1)⟩,[2]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[5,2],(-1)⟩,[32]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[5,1,1],(1)⟩,[34]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[4,3],(-1)⟩,[85]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[4,2,1],(1)⟩,[87]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[4,1,1,1],(-1)⟩,[89]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[3,3,1],(1)⟩,[149]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[3,2,2],(1)⟩,[151]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[3,2,1,1],(-1)⟩,[153]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[3,1,1,1,1],(1)⟩,[155]⟩
]

def block18 : Array IndexedEntry := #[
  ⟨⟨[1,1,1,1,1,1,1],[2,2,2,1],(-1)⟩,[223]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[2,2,1,1,1],(1)⟩,[225]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[2,1,1,1,1,1],(-1)⟩,[227]⟩,
  ⟨⟨[1,1,1,1,1,1,1],[1,1,1,1,1,1,1],(1)⟩,[275]⟩
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
  | 10 => block10
  | 11 => block11
  | 12 => block12
  | 13 => block13
  | 14 => block14
  | 15 => block15
  | _ => #[]

def blockGroup1 : ℕ → Array IndexedEntry
  | 0 => block16
  | 1 => block17
  | 2 => block18
  | _ => #[]

def superGroup0 (k : ℕ) : Array IndexedEntry :=
  match (k/16)%16 with
  | 0 => blockGroup0 (k%16)
  | 1 => blockGroup1 (k%16)
  | _ => #[]

def table : IndexedTable := ⟨292, fun k =>
  match k/256 with
  | 0 => superGroup0 k
  | _ => #[]⟩

theorem group0_checked : checkIndexedGroup table 0 = true := by decide
theorem group1_checked : checkIndexedGroup table 1 = true := by decide

theorem table_checked : checkIndexedTable table = true := by
  unfold checkIndexedTable
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 2 := by simpa [table] using List.mem_range.mp hk
  interval_cases k
  · exact group0_checked
  · exact group1_checked

def classes : List Shape := [[7],[6,1],[5,2],[5,1,1],[4,3],[4,2,1],[4,1,1,1],[3,3,1],[3,2,2],[3,2,1,1],[3,1,1,1,1],[2,2,2,1],[2,2,1,1,1],[2,1,1,1,1,1],[1,1,1,1,1,1,1]]
theorem classes_checked : checkClasses 7 classes = true := by decide

def refs0 : List ℕ := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def refs1 : List ℕ := [30,31,33,35,37,39,41,43,45,47,49,51,53,55,57]
def refs2 : List ℕ := [58,59,60,61,62,63,64,66,68,70,72,74,76,78,80]
def refs3 : List ℕ := [81,82,83,84,86,88,90,92,94,96,98,100,102,104,106]
def refs4 : List ℕ := [107,108,109,110,111,112,113,114,115,116,117,118,119,120,122]
def refs5 : List ℕ := [123,124,125,126,127,128,129,130,131,132,133,135,137,139,141]
def refs6 : List ℕ := [142,143,144,145,146,147,148,150,152,154,156,158,160,162,164]
def refs7 : List ℕ := [165,166,167,168,169,170,171,172,173,174,175,176,177,178,179]
def refs8 : List ℕ := [180,181,182,183,184,185,186,187,188,189,190,191,192,193,195]
def refs9 : List ℕ := [196,197,198,199,200,201,202,203,204,205,206,207,208,209,211]
def refs10 : List ℕ := [212,213,214,215,216,217,218,219,220,221,222,224,226,228,230]
def refs11 : List ℕ := [231,232,233,234,235,236,237,238,239,240,241,242,243,244,245]
def refs12 : List ℕ := [246,247,248,249,250,251,252,253,254,255,256,257,258,259,260]
def refs13 : List ℕ := [261,262,263,264,265,266,267,268,269,270,271,272,273,274,276]
def refs14 : List ℕ := [277,278,279,280,281,282,283,284,285,286,287,288,289,290,291]
theorem row0_checked : checkIndexedRow table [7] classes refs0 = true := by decide
theorem residue0_checked : (2 * indexedCoverSum table 7 classes refs5 refs0) % 1000000007 ≠ 0 := by decide

theorem row1_checked : checkIndexedRow table [6,1] classes refs1 = true := by decide
theorem residue1_checked : (2 * indexedCoverSum table 7 classes refs5 refs1) % 1000000007 ≠ 0 := by decide

theorem row2_checked : checkIndexedRow table [5,2] classes refs2 = true := by decide
theorem residue2_checked : (2 * indexedCoverSum table 7 classes refs5 refs2) % 1000000007 ≠ 0 := by decide

theorem row3_checked : checkIndexedRow table [5,1,1] classes refs3 = true := by decide
theorem residue3_checked : (2 * indexedCoverSum table 7 classes refs5 refs3) % 1000000007 ≠ 0 := by decide

theorem row4_checked : checkIndexedRow table [4,3] classes refs4 = true := by decide
theorem residue4_checked : (2 * indexedCoverSum table 7 classes refs5 refs4) % 1000000007 ≠ 0 := by decide

theorem row5_checked : checkIndexedRow table [4,2,1] classes refs5 = true := by decide
theorem residue5_checked : (2 * indexedCoverSum table 7 classes refs5 refs5) % 1000000007 ≠ 0 := by decide

theorem row6_checked : checkIndexedRow table [4,1,1,1] classes refs6 = true := by decide
theorem residue6_checked : (2 * indexedCoverSum table 7 classes refs5 refs6) % 1000000007 ≠ 0 := by decide

theorem row7_checked : checkIndexedRow table [3,3,1] classes refs7 = true := by decide
theorem residue7_checked : (2 * indexedCoverSum table 7 classes refs5 refs7) % 1000000007 ≠ 0 := by decide

theorem row8_checked : checkIndexedRow table [3,2,2] classes refs8 = true := by decide
theorem residue8_checked : (2 * indexedCoverSum table 7 classes refs5 refs8) % 1000000007 ≠ 0 := by decide

theorem row9_checked : checkIndexedRow table [3,2,1,1] classes refs9 = true := by decide
theorem residue9_checked : (2 * indexedCoverSum table 7 classes refs5 refs9) % 1000000007 ≠ 0 := by decide

theorem row10_checked : checkIndexedRow table [3,1,1,1,1] classes refs10 = true := by decide
theorem residue10_checked : (2 * indexedCoverSum table 7 classes refs5 refs10) % 1000000007 ≠ 0 := by decide

theorem row11_checked : checkIndexedRow table [2,2,2,1] classes refs11 = true := by decide
theorem residue11_checked : (2 * indexedCoverSum table 7 classes refs5 refs11) % 1000000007 ≠ 0 := by decide

theorem row12_checked : checkIndexedRow table [2,2,1,1,1] classes refs12 = true := by decide
theorem residue12_checked : (2 * indexedCoverSum table 7 classes refs5 refs12) % 1000000007 ≠ 0 := by decide

theorem row13_checked : checkIndexedRow table [2,1,1,1,1,1] classes refs13 = true := by decide
theorem residue13_checked : (2 * indexedCoverSum table 7 classes refs5 refs13) % 1000000007 ≠ 0 := by decide

theorem row14_checked : checkIndexedRow table [1,1,1,1,1,1,1] classes refs14 = true := by decide
theorem residue14_checked : (2 * indexedCoverSum table 7 classes refs5 refs14) % 1000000007 ≠ 0 := by decide

theorem norm_checked : 2 * indexedNormSum table 7 classes refs5 = ((7 : ℕ).factorial : ℤ) := by decide

theorem targets_checked : ∀ nu ∈ classes, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 7 classes refs5 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classes, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact ⟨refs11, row11_checked, residue11_checked⟩
  · exact ⟨refs12, row12_checked, residue12_checked⟩
  · exact ⟨refs13, row13_checked, residue13_checked⟩
  · exact ⟨refs14, row14_checked, residue14_checked⟩

def witness : Nat.Partition 7 where
  parts := [4,2,1]
  parts_pos := by decide
  parts_sum := rfl

theorem witness_rows : partitionRows witness = [4,2,1] := by
  change ([4,2,1] : Multiset ℕ).sort (· ≥ ·) = [4,2,1]
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (by simp)

theorem norm : evenNormNumerator witness = ((7 : ℕ).factorial : ℤ) := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs5 = true := by
    rw [witness_rows]; exact row5_checked
  rw [← indexedNorm_eq_evenNorm (by decide) table table_checked classes classes_checked witness refs5 hr]
  exact norm_checked

theorem cover_residue (nu : Nat.Partition 7) :
    evenCoverNumerator witness nu % 1000000007 ≠ 0 := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs5 = true := by
    rw [witness_rows]; exact row5_checked
  obtain ⟨refs, hp, he⟩ := targets_checked (partitionRows nu)
    (checkClasses_complete classes classes_checked nu)
  rw [← indexedCover_eq_evenCover (by decide) table table_checked classes classes_checked witness nu refs5 refs hr hp]
  exact he

end HSTZ.TauCetiFinite.D7
#print axioms HSTZ.TauCetiFinite.D7.table_checked
#print axioms HSTZ.TauCetiFinite.D7.classes_checked
#print axioms HSTZ.TauCetiFinite.D7.norm_checked
#print axioms HSTZ.TauCetiFinite.D7.targets_checked
#print axioms HSTZ.TauCetiFinite.D7.norm
#print axioms HSTZ.TauCetiFinite.D7.cover_residue
