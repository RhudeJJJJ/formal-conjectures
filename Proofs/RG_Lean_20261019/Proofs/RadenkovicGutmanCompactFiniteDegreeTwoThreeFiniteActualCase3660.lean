/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3660 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap3660 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3660 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3660_checked : acceptsGraphIso
    (source (graph core3660) (root 6) 0 7) DegreeTwoThreeSpectrum4210.graph sourceMap3660=true := by decide +kernel
theorem fusedMap3660_checked : acceptsGraphIso
    (fused (graph core3660) (root 6) 0 7) DegreeTwoThreeSpectrum3897.graph fusedMap3660=true := by decide +kernel
theorem certified3660 : Certified (graph core3660) (root 6) 0 7 :=
  of_native_maps core3660 DegreeTwoThreeSpectrum4210.graph DegreeTwoThreeSpectrum3897.graph
    sourceMap3660 fusedMap3660 sourceMap3660_checked fusedMap3660_checked
    DegreeTwoThreeFiniteComparisons.comparison3660
#print axioms sourceMap3660_checked
#print axioms fusedMap3660_checked
#print axioms certified3660
def sourceMap3660swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,10] (sourceLabel 6 7 0 v)
def fusedMap3660swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3660swap_checked : acceptsGraphIso
    (source (graph core3660) (root 6) 7 0) DegreeTwoThreeSpectrum4210.graph sourceMap3660swap=true := by decide +kernel
theorem fusedMap3660swap_checked : acceptsGraphIso
    (fused (graph core3660) (root 6) 7 0) DegreeTwoThreeSpectrum3897.graph fusedMap3660swap=true := by decide +kernel
theorem certified3660swap : Certified (graph core3660) (root 6) 7 0 :=
  of_native_maps core3660 DegreeTwoThreeSpectrum4210.graph DegreeTwoThreeSpectrum3897.graph
    sourceMap3660swap fusedMap3660swap sourceMap3660swap_checked fusedMap3660swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3660
#print axioms sourceMap3660swap_checked
#print axioms fusedMap3660swap_checked
#print axioms certified3660swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
