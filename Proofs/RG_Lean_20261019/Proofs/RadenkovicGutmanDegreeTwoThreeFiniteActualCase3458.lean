/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3458 : Family 9 := level9.get ⟨636,by decide⟩
def sourceMap3458 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3458 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3458_checked : acceptsGraphIso
    (source (graph core3458) (root 9) 0 5) DegreeTwoThreeSpectrum6494.graph sourceMap3458=true := by decide +kernel
theorem fusedMap3458_checked : acceptsGraphIso
    (fused (graph core3458) (root 9) 0 5) DegreeTwoThreeSpectrum6495.graph fusedMap3458=true := by decide +kernel
theorem certified3458 : Certified (graph core3458) (root 9) 0 5 :=
  of_native_maps core3458 DegreeTwoThreeSpectrum6494.graph DegreeTwoThreeSpectrum6495.graph
    sourceMap3458 fusedMap3458 sourceMap3458_checked fusedMap3458_checked
    DegreeTwoThreeFiniteComparisons.comparison3458
#print axioms sourceMap3458_checked
#print axioms fusedMap3458_checked
#print axioms certified3458
def sourceMap3458swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3458swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3458swap_checked : acceptsGraphIso
    (source (graph core3458) (root 9) 5 0) DegreeTwoThreeSpectrum6494.graph sourceMap3458swap=true := by decide +kernel
theorem fusedMap3458swap_checked : acceptsGraphIso
    (fused (graph core3458) (root 9) 5 0) DegreeTwoThreeSpectrum6495.graph fusedMap3458swap=true := by decide +kernel
theorem certified3458swap : Certified (graph core3458) (root 9) 5 0 :=
  of_native_maps core3458 DegreeTwoThreeSpectrum6494.graph DegreeTwoThreeSpectrum6495.graph
    sourceMap3458swap fusedMap3458swap sourceMap3458swap_checked fusedMap3458swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3458
#print axioms sourceMap3458swap_checked
#print axioms fusedMap3458swap_checked
#print axioms certified3458swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
