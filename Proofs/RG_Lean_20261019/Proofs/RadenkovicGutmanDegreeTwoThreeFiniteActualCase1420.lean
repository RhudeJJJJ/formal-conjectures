/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1420 : Family 9 := level9.get ⟨651,by decide⟩
def sourceMap1420 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1420 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1420_checked : acceptsGraphIso
    (source (graph core1420) (root 9) 0 2) DegreeTwoThreeSpectrum2296.graph sourceMap1420=true := by decide +kernel
theorem fusedMap1420_checked : acceptsGraphIso
    (fused (graph core1420) (root 9) 0 2) DegreeTwoThreeSpectrum2113.graph fusedMap1420=true := by decide +kernel
theorem certified1420 : Certified (graph core1420) (root 9) 0 2 :=
  of_native_maps core1420 DegreeTwoThreeSpectrum2296.graph DegreeTwoThreeSpectrum2113.graph
    sourceMap1420 fusedMap1420 sourceMap1420_checked fusedMap1420_checked
    DegreeTwoThreeFiniteComparisons.comparison1420
#print axioms sourceMap1420_checked
#print axioms fusedMap1420_checked
#print axioms certified1420
def sourceMap1420swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1420swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1420swap_checked : acceptsGraphIso
    (source (graph core1420) (root 9) 2 0) DegreeTwoThreeSpectrum2296.graph sourceMap1420swap=true := by decide +kernel
theorem fusedMap1420swap_checked : acceptsGraphIso
    (fused (graph core1420) (root 9) 2 0) DegreeTwoThreeSpectrum2113.graph fusedMap1420swap=true := by decide +kernel
theorem certified1420swap : Certified (graph core1420) (root 9) 2 0 :=
  of_native_maps core1420 DegreeTwoThreeSpectrum2296.graph DegreeTwoThreeSpectrum2113.graph
    sourceMap1420swap fusedMap1420swap sourceMap1420swap_checked fusedMap1420swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1420
#print axioms sourceMap1420swap_checked
#print axioms fusedMap1420swap_checked
#print axioms certified1420swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
