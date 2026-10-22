/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1396 : Family 9 := level9.get ⟨591,by decide⟩
def sourceMap1396 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1396 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1396_checked : acceptsGraphIso
    (source (graph core1396) (root 9) 0 2) DegreeTwoThreeSpectrum2268.graph sourceMap1396=true := by decide +kernel
theorem fusedMap1396_checked : acceptsGraphIso
    (fused (graph core1396) (root 9) 0 2) DegreeTwoThreeSpectrum1993.graph fusedMap1396=true := by decide +kernel
theorem certified1396 : Certified (graph core1396) (root 9) 0 2 :=
  of_native_maps core1396 DegreeTwoThreeSpectrum2268.graph DegreeTwoThreeSpectrum1993.graph
    sourceMap1396 fusedMap1396 sourceMap1396_checked fusedMap1396_checked
    DegreeTwoThreeFiniteComparisons.comparison1396
#print axioms sourceMap1396_checked
#print axioms fusedMap1396_checked
#print axioms certified1396
def sourceMap1396swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1396swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1396swap_checked : acceptsGraphIso
    (source (graph core1396) (root 9) 2 0) DegreeTwoThreeSpectrum2268.graph sourceMap1396swap=true := by decide +kernel
theorem fusedMap1396swap_checked : acceptsGraphIso
    (fused (graph core1396) (root 9) 2 0) DegreeTwoThreeSpectrum1993.graph fusedMap1396swap=true := by decide +kernel
theorem certified1396swap : Certified (graph core1396) (root 9) 2 0 :=
  of_native_maps core1396 DegreeTwoThreeSpectrum2268.graph DegreeTwoThreeSpectrum1993.graph
    sourceMap1396swap fusedMap1396swap sourceMap1396swap_checked fusedMap1396swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1396
#print axioms sourceMap1396swap_checked
#print axioms fusedMap1396swap_checked
#print axioms certified1396swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
