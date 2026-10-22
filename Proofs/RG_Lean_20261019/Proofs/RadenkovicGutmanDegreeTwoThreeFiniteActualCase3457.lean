/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3457 : Family 9 := level9.get ⟨635,by decide⟩
def sourceMap3457 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3457 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3457_checked : acceptsGraphIso
    (source (graph core3457) (root 9) 0 5) DegreeTwoThreeSpectrum6488.graph sourceMap3457=true := by decide +kernel
theorem fusedMap3457_checked : acceptsGraphIso
    (fused (graph core3457) (root 9) 0 5) DegreeTwoThreeSpectrum6489.graph fusedMap3457=true := by decide +kernel
theorem certified3457 : Certified (graph core3457) (root 9) 0 5 :=
  of_native_maps core3457 DegreeTwoThreeSpectrum6488.graph DegreeTwoThreeSpectrum6489.graph
    sourceMap3457 fusedMap3457 sourceMap3457_checked fusedMap3457_checked
    DegreeTwoThreeFiniteComparisons.comparison3457
#print axioms sourceMap3457_checked
#print axioms fusedMap3457_checked
#print axioms certified3457
def sourceMap3457swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3457swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3457swap_checked : acceptsGraphIso
    (source (graph core3457) (root 9) 5 0) DegreeTwoThreeSpectrum6488.graph sourceMap3457swap=true := by decide +kernel
theorem fusedMap3457swap_checked : acceptsGraphIso
    (fused (graph core3457) (root 9) 5 0) DegreeTwoThreeSpectrum6489.graph fusedMap3457swap=true := by decide +kernel
theorem certified3457swap : Certified (graph core3457) (root 9) 5 0 :=
  of_native_maps core3457 DegreeTwoThreeSpectrum6488.graph DegreeTwoThreeSpectrum6489.graph
    sourceMap3457swap fusedMap3457swap sourceMap3457swap_checked fusedMap3457swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3457
#print axioms sourceMap3457swap_checked
#print axioms fusedMap3457swap_checked
#print axioms certified3457swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
