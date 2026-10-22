/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1282 : Family 9 := level9.get ⟨305,by decide⟩
def sourceMap1282 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,5,6,7,8,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1282 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,5,6,7,1,2,3,4] (fusedLabel 9 0 2 v)
theorem sourceMap1282_checked : acceptsGraphIso
    (source (graph core1282) (root 9) 0 2) DegreeTwoThreeSpectrum2200.graph sourceMap1282=true := by decide +kernel
theorem fusedMap1282_checked : acceptsGraphIso
    (fused (graph core1282) (root 9) 0 2) DegreeTwoThreeSpectrum1910.graph fusedMap1282=true := by decide +kernel
theorem certified1282 : Certified (graph core1282) (root 9) 0 2 :=
  of_native_maps core1282 DegreeTwoThreeSpectrum2200.graph DegreeTwoThreeSpectrum1910.graph
    sourceMap1282 fusedMap1282 sourceMap1282_checked fusedMap1282_checked
    DegreeTwoThreeFiniteComparisons.comparison1282
#print axioms sourceMap1282_checked
#print axioms fusedMap1282_checked
#print axioms certified1282
def sourceMap1282swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,5,6,7,2,3,4,8] (sourceLabel 9 2 0 v)
def fusedMap1282swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,5,6,7,1,2,3,4] (fusedLabel 9 2 0 v)
theorem sourceMap1282swap_checked : acceptsGraphIso
    (source (graph core1282) (root 9) 2 0) DegreeTwoThreeSpectrum2200.graph sourceMap1282swap=true := by decide +kernel
theorem fusedMap1282swap_checked : acceptsGraphIso
    (fused (graph core1282) (root 9) 2 0) DegreeTwoThreeSpectrum1910.graph fusedMap1282swap=true := by decide +kernel
theorem certified1282swap : Certified (graph core1282) (root 9) 2 0 :=
  of_native_maps core1282 DegreeTwoThreeSpectrum2200.graph DegreeTwoThreeSpectrum1910.graph
    sourceMap1282swap fusedMap1282swap sourceMap1282swap_checked fusedMap1282swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1282
#print axioms sourceMap1282swap_checked
#print axioms fusedMap1282swap_checked
#print axioms certified1282swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
