/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1377 : Family 9 := level9.get ⟨547,by decide⟩
def sourceMap1377 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1377 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1377_checked : acceptsGraphIso
    (source (graph core1377) (root 9) 0 2) DegreeTwoThreeSpectrum2246.graph sourceMap1377=true := by decide +kernel
theorem fusedMap1377_checked : acceptsGraphIso
    (fused (graph core1377) (root 9) 0 2) DegreeTwoThreeSpectrum1927.graph fusedMap1377=true := by decide +kernel
theorem certified1377 : Certified (graph core1377) (root 9) 0 2 :=
  of_native_maps core1377 DegreeTwoThreeSpectrum2246.graph DegreeTwoThreeSpectrum1927.graph
    sourceMap1377 fusedMap1377 sourceMap1377_checked fusedMap1377_checked
    DegreeTwoThreeFiniteComparisons.comparison1377
#print axioms sourceMap1377_checked
#print axioms fusedMap1377_checked
#print axioms certified1377
def sourceMap1377swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1377swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1377swap_checked : acceptsGraphIso
    (source (graph core1377) (root 9) 2 0) DegreeTwoThreeSpectrum2246.graph sourceMap1377swap=true := by decide +kernel
theorem fusedMap1377swap_checked : acceptsGraphIso
    (fused (graph core1377) (root 9) 2 0) DegreeTwoThreeSpectrum1927.graph fusedMap1377swap=true := by decide +kernel
theorem certified1377swap : Certified (graph core1377) (root 9) 2 0 :=
  of_native_maps core1377 DegreeTwoThreeSpectrum2246.graph DegreeTwoThreeSpectrum1927.graph
    sourceMap1377swap fusedMap1377swap sourceMap1377swap_checked fusedMap1377swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1377
#print axioms sourceMap1377swap_checked
#print axioms fusedMap1377swap_checked
#print axioms certified1377swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
