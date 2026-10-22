/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3054 : Family 10 := level10.get ⟨1713,by decide⟩
def sourceMap3054 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3054 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3054_checked : acceptsGraphIso
    (source (graph core3054) (root 10) 0 4) DegreeTwoThreeSpectrum7334.graph sourceMap3054=true := by decide +kernel
theorem fusedMap3054_checked : acceptsGraphIso
    (fused (graph core3054) (root 10) 0 4) DegreeTwoThreeSpectrum6492.graph fusedMap3054=true := by decide +kernel
theorem certified3054 : Certified (graph core3054) (root 10) 0 4 :=
  of_native_maps core3054 DegreeTwoThreeSpectrum7334.graph DegreeTwoThreeSpectrum6492.graph
    sourceMap3054 fusedMap3054 sourceMap3054_checked fusedMap3054_checked
    DegreeTwoThreeFiniteComparisons.comparison3054
#print axioms sourceMap3054_checked
#print axioms fusedMap3054_checked
#print axioms certified3054
def sourceMap3054swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3054swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3054swap_checked : acceptsGraphIso
    (source (graph core3054) (root 10) 4 0) DegreeTwoThreeSpectrum7334.graph sourceMap3054swap=true := by decide +kernel
theorem fusedMap3054swap_checked : acceptsGraphIso
    (fused (graph core3054) (root 10) 4 0) DegreeTwoThreeSpectrum6492.graph fusedMap3054swap=true := by decide +kernel
theorem certified3054swap : Certified (graph core3054) (root 10) 4 0 :=
  of_native_maps core3054 DegreeTwoThreeSpectrum7334.graph DegreeTwoThreeSpectrum6492.graph
    sourceMap3054swap fusedMap3054swap sourceMap3054swap_checked fusedMap3054swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3054
#print axioms sourceMap3054swap_checked
#print axioms fusedMap3054swap_checked
#print axioms certified3054swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
