/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3590 : Family 8 := level8.get ⟨165,by decide⟩
def sourceMap3590 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3590 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3590_checked : acceptsGraphIso
    (source (graph core3590) (root 8) 0 6) DegreeTwoThreeSpectrum5681.graph sourceMap3590=true := by decide +kernel
theorem fusedMap3590_checked : acceptsGraphIso
    (fused (graph core3590) (root 8) 0 6) DegreeTwoThreeSpectrum5683.graph fusedMap3590=true := by decide +kernel
theorem certified3590 : Certified (graph core3590) (root 8) 0 6 :=
  of_native_maps core3590 DegreeTwoThreeSpectrum5681.graph DegreeTwoThreeSpectrum5683.graph
    sourceMap3590 fusedMap3590 sourceMap3590_checked fusedMap3590_checked
    DegreeTwoThreeFiniteComparisons.comparison3590
#print axioms sourceMap3590_checked
#print axioms fusedMap3590_checked
#print axioms certified3590
def sourceMap3590swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3590swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3590swap_checked : acceptsGraphIso
    (source (graph core3590) (root 8) 6 0) DegreeTwoThreeSpectrum5681.graph sourceMap3590swap=true := by decide +kernel
theorem fusedMap3590swap_checked : acceptsGraphIso
    (fused (graph core3590) (root 8) 6 0) DegreeTwoThreeSpectrum5683.graph fusedMap3590swap=true := by decide +kernel
theorem certified3590swap : Certified (graph core3590) (root 8) 6 0 :=
  of_native_maps core3590 DegreeTwoThreeSpectrum5681.graph DegreeTwoThreeSpectrum5683.graph
    sourceMap3590swap fusedMap3590swap sourceMap3590swap_checked fusedMap3590swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3590
#print axioms sourceMap3590swap_checked
#print axioms fusedMap3590swap_checked
#print axioms certified3590swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
