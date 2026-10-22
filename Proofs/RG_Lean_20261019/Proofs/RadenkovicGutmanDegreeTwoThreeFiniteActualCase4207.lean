/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4207 : Family 9 := level9.get ⟨73,by decide⟩
def sourceMap4207 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4207 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4207_checked : acceptsGraphIso
    (source (graph core4207) (root 9) 2 2) DegreeTwoThreeSpectrum4437.graph sourceMap4207=true := by decide +kernel
theorem fusedMap4207_checked : acceptsGraphIso
    (fused (graph core4207) (root 9) 2 2) DegreeTwoThreeSpectrum4000.graph fusedMap4207=true := by decide +kernel
theorem certified4207 : Certified (graph core4207) (root 9) 2 2 :=
  of_native_maps core4207 DegreeTwoThreeSpectrum4437.graph DegreeTwoThreeSpectrum4000.graph
    sourceMap4207 fusedMap4207 sourceMap4207_checked fusedMap4207_checked
    DegreeTwoThreeFiniteComparisons.comparison4207
#print axioms sourceMap4207_checked
#print axioms fusedMap4207_checked
#print axioms certified4207
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
