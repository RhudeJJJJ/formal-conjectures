/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3650 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap3650 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3650 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3650_checked : acceptsGraphIso
    (source (graph core3650) (root 6) 0 7) DegreeTwoThreeSpectrum4127.graph sourceMap3650=true := by decide +kernel
theorem fusedMap3650_checked : acceptsGraphIso
    (fused (graph core3650) (root 6) 0 7) DegreeTwoThreeSpectrum3877.graph fusedMap3650=true := by decide +kernel
theorem certified3650 : Certified (graph core3650) (root 6) 0 7 :=
  of_native_maps core3650 DegreeTwoThreeSpectrum4127.graph DegreeTwoThreeSpectrum3877.graph
    sourceMap3650 fusedMap3650 sourceMap3650_checked fusedMap3650_checked
    DegreeTwoThreeFiniteComparisons.comparison3650
#print axioms sourceMap3650_checked
#print axioms fusedMap3650_checked
#print axioms certified3650
def sourceMap3650swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3650swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3650swap_checked : acceptsGraphIso
    (source (graph core3650) (root 6) 7 0) DegreeTwoThreeSpectrum4127.graph sourceMap3650swap=true := by decide +kernel
theorem fusedMap3650swap_checked : acceptsGraphIso
    (fused (graph core3650) (root 6) 7 0) DegreeTwoThreeSpectrum3877.graph fusedMap3650swap=true := by decide +kernel
theorem certified3650swap : Certified (graph core3650) (root 6) 7 0 :=
  of_native_maps core3650 DegreeTwoThreeSpectrum4127.graph DegreeTwoThreeSpectrum3877.graph
    sourceMap3650swap fusedMap3650swap sourceMap3650swap_checked fusedMap3650swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3650
#print axioms sourceMap3650swap_checked
#print axioms fusedMap3650swap_checked
#print axioms certified3650swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
