/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3002 : Family 10 := level10.get ⟨1574,by decide⟩
def sourceMap3002 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3002 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3002_checked : acceptsGraphIso
    (source (graph core3002) (root 10) 0 4) DegreeTwoThreeSpectrum7113.graph sourceMap3002=true := by decide +kernel
theorem fusedMap3002_checked : acceptsGraphIso
    (fused (graph core3002) (root 10) 0 4) DegreeTwoThreeSpectrum6055.graph fusedMap3002=true := by decide +kernel
theorem certified3002 : Certified (graph core3002) (root 10) 0 4 :=
  of_native_maps core3002 DegreeTwoThreeSpectrum7113.graph DegreeTwoThreeSpectrum6055.graph
    sourceMap3002 fusedMap3002 sourceMap3002_checked fusedMap3002_checked
    DegreeTwoThreeFiniteComparisons.comparison3002
#print axioms sourceMap3002_checked
#print axioms fusedMap3002_checked
#print axioms certified3002
def sourceMap3002swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3002swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3002swap_checked : acceptsGraphIso
    (source (graph core3002) (root 10) 4 0) DegreeTwoThreeSpectrum7113.graph sourceMap3002swap=true := by decide +kernel
theorem fusedMap3002swap_checked : acceptsGraphIso
    (fused (graph core3002) (root 10) 4 0) DegreeTwoThreeSpectrum6055.graph fusedMap3002swap=true := by decide +kernel
theorem certified3002swap : Certified (graph core3002) (root 10) 4 0 :=
  of_native_maps core3002 DegreeTwoThreeSpectrum7113.graph DegreeTwoThreeSpectrum6055.graph
    sourceMap3002swap fusedMap3002swap sourceMap3002swap_checked fusedMap3002swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3002
#print axioms sourceMap3002swap_checked
#print axioms fusedMap3002swap_checked
#print axioms certified3002swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
