/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1376 : Family 9 := level9.get ⟨544,by decide⟩
def sourceMap1376 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1376 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1376_checked : acceptsGraphIso
    (source (graph core1376) (root 9) 0 2) DegreeTwoThreeSpectrum2243.graph sourceMap1376=true := by decide +kernel
theorem fusedMap1376_checked : acceptsGraphIso
    (fused (graph core1376) (root 9) 0 2) DegreeTwoThreeSpectrum1925.graph fusedMap1376=true := by decide +kernel
theorem certified1376 : Certified (graph core1376) (root 9) 0 2 :=
  of_native_maps core1376 DegreeTwoThreeSpectrum2243.graph DegreeTwoThreeSpectrum1925.graph
    sourceMap1376 fusedMap1376 sourceMap1376_checked fusedMap1376_checked
    DegreeTwoThreeFiniteComparisons.comparison1376
#print axioms sourceMap1376_checked
#print axioms fusedMap1376_checked
#print axioms certified1376
def sourceMap1376swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1376swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1376swap_checked : acceptsGraphIso
    (source (graph core1376) (root 9) 2 0) DegreeTwoThreeSpectrum2243.graph sourceMap1376swap=true := by decide +kernel
theorem fusedMap1376swap_checked : acceptsGraphIso
    (fused (graph core1376) (root 9) 2 0) DegreeTwoThreeSpectrum1925.graph fusedMap1376swap=true := by decide +kernel
theorem certified1376swap : Certified (graph core1376) (root 9) 2 0 :=
  of_native_maps core1376 DegreeTwoThreeSpectrum2243.graph DegreeTwoThreeSpectrum1925.graph
    sourceMap1376swap fusedMap1376swap sourceMap1376swap_checked fusedMap1376swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1376
#print axioms sourceMap1376swap_checked
#print axioms fusedMap1376swap_checked
#print axioms certified1376swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
