/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3092 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap3092 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3092 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3092_checked : acceptsGraphIso
    (source (graph core3092) (root 6) 0 5) DegreeTwoThreeSpectrum1748.graph sourceMap3092=true := by decide +kernel
theorem fusedMap3092_checked : acceptsGraphIso
    (fused (graph core3092) (root 6) 0 5) DegreeTwoThreeSpectrum1750.graph fusedMap3092=true := by decide +kernel
theorem certified3092 : Certified (graph core3092) (root 6) 0 5 :=
  of_native_maps core3092 DegreeTwoThreeSpectrum1748.graph DegreeTwoThreeSpectrum1750.graph
    sourceMap3092 fusedMap3092 sourceMap3092_checked fusedMap3092_checked
    DegreeTwoThreeFiniteComparisons.comparison3092
#print axioms sourceMap3092_checked
#print axioms fusedMap3092_checked
#print axioms certified3092
def sourceMap3092swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3092swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3092swap_checked : acceptsGraphIso
    (source (graph core3092) (root 6) 5 0) DegreeTwoThreeSpectrum1748.graph sourceMap3092swap=true := by decide +kernel
theorem fusedMap3092swap_checked : acceptsGraphIso
    (fused (graph core3092) (root 6) 5 0) DegreeTwoThreeSpectrum1750.graph fusedMap3092swap=true := by decide +kernel
theorem certified3092swap : Certified (graph core3092) (root 6) 5 0 :=
  of_native_maps core3092 DegreeTwoThreeSpectrum1748.graph DegreeTwoThreeSpectrum1750.graph
    sourceMap3092swap fusedMap3092swap sourceMap3092swap_checked fusedMap3092swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3092
#print axioms sourceMap3092swap_checked
#print axioms fusedMap3092swap_checked
#print axioms certified3092swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
