/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3474 : Family 9 := level9.get ⟨696,by decide⟩
def sourceMap3474 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3474 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3474_checked : acceptsGraphIso
    (source (graph core3474) (root 9) 0 5) DegreeTwoThreeSpectrum7083.graph sourceMap3474=true := by decide +kernel
theorem fusedMap3474_checked : acceptsGraphIso
    (fused (graph core3474) (root 9) 0 5) DegreeTwoThreeSpectrum5993.graph fusedMap3474=true := by decide +kernel
theorem certified3474 : Certified (graph core3474) (root 9) 0 5 :=
  of_native_maps core3474 DegreeTwoThreeSpectrum7083.graph DegreeTwoThreeSpectrum5993.graph
    sourceMap3474 fusedMap3474 sourceMap3474_checked fusedMap3474_checked
    DegreeTwoThreeFiniteComparisons.comparison3474
#print axioms sourceMap3474_checked
#print axioms fusedMap3474_checked
#print axioms certified3474
def sourceMap3474swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,13,14,15,16,12] (sourceLabel 9 5 0 v)
def fusedMap3474swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3474swap_checked : acceptsGraphIso
    (source (graph core3474) (root 9) 5 0) DegreeTwoThreeSpectrum7083.graph sourceMap3474swap=true := by decide +kernel
theorem fusedMap3474swap_checked : acceptsGraphIso
    (fused (graph core3474) (root 9) 5 0) DegreeTwoThreeSpectrum5993.graph fusedMap3474swap=true := by decide +kernel
theorem certified3474swap : Certified (graph core3474) (root 9) 5 0 :=
  of_native_maps core3474 DegreeTwoThreeSpectrum7083.graph DegreeTwoThreeSpectrum5993.graph
    sourceMap3474swap fusedMap3474swap sourceMap3474swap_checked fusedMap3474swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3474
#print axioms sourceMap3474swap_checked
#print axioms fusedMap3474swap_checked
#print axioms certified3474swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
