/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3990 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3990 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,8,6,7,1,0,9,10,11,12,13] (sourceLabel 4 1 6 v)
def fusedMap3990 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 1 6 v)
theorem sourceMap3990_checked : acceptsGraphIso
    (source (graph core3990) (root 4) 1 6) DegreeTwoThreeSpectrum1758.graph sourceMap3990=true := by decide +kernel
theorem fusedMap3990_checked : acceptsGraphIso
    (fused (graph core3990) (root 4) 1 6) DegreeTwoThreeSpectrum1710.graph fusedMap3990=true := by decide +kernel
theorem certified3990 : Certified (graph core3990) (root 4) 1 6 :=
  of_native_maps core3990 DegreeTwoThreeSpectrum1758.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap3990 fusedMap3990 sourceMap3990_checked fusedMap3990_checked
    DegreeTwoThreeFiniteComparisons.comparison3990
#print axioms sourceMap3990_checked
#print axioms fusedMap3990_checked
#print axioms certified3990
def sourceMap3990swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 2) → Fin 14 :=
  fun v => ![2,3,4,5,8,1,0,9,10,11,12,13,6,7] (sourceLabel 4 6 1 v)
def fusedMap3990swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 6 1 v)
theorem sourceMap3990swap_checked : acceptsGraphIso
    (source (graph core3990) (root 4) 6 1) DegreeTwoThreeSpectrum1758.graph sourceMap3990swap=true := by decide +kernel
theorem fusedMap3990swap_checked : acceptsGraphIso
    (fused (graph core3990) (root 4) 6 1) DegreeTwoThreeSpectrum1710.graph fusedMap3990swap=true := by decide +kernel
theorem certified3990swap : Certified (graph core3990) (root 4) 6 1 :=
  of_native_maps core3990 DegreeTwoThreeSpectrum1758.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap3990swap fusedMap3990swap sourceMap3990swap_checked fusedMap3990swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3990
#print axioms sourceMap3990swap_checked
#print axioms fusedMap3990swap_checked
#print axioms certified3990swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
