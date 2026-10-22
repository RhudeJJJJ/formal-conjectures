/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1404 : Family 9 := level9.get ⟨605,by decide⟩
def sourceMap1404 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1404 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1404_checked : acceptsGraphIso
    (source (graph core1404) (root 9) 0 2) DegreeTwoThreeSpectrum2276.graph sourceMap1404=true := by decide +kernel
theorem fusedMap1404_checked : acceptsGraphIso
    (fused (graph core1404) (root 9) 0 2) DegreeTwoThreeSpectrum2012.graph fusedMap1404=true := by decide +kernel
theorem certified1404 : Certified (graph core1404) (root 9) 0 2 :=
  of_native_maps core1404 DegreeTwoThreeSpectrum2276.graph DegreeTwoThreeSpectrum2012.graph
    sourceMap1404 fusedMap1404 sourceMap1404_checked fusedMap1404_checked
    DegreeTwoThreeFiniteComparisons.comparison1404
#print axioms sourceMap1404_checked
#print axioms fusedMap1404_checked
#print axioms certified1404
def sourceMap1404swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1404swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1404swap_checked : acceptsGraphIso
    (source (graph core1404) (root 9) 2 0) DegreeTwoThreeSpectrum2276.graph sourceMap1404swap=true := by decide +kernel
theorem fusedMap1404swap_checked : acceptsGraphIso
    (fused (graph core1404) (root 9) 2 0) DegreeTwoThreeSpectrum2012.graph fusedMap1404swap=true := by decide +kernel
theorem certified1404swap : Certified (graph core1404) (root 9) 2 0 :=
  of_native_maps core1404 DegreeTwoThreeSpectrum2276.graph DegreeTwoThreeSpectrum2012.graph
    sourceMap1404swap fusedMap1404swap sourceMap1404swap_checked fusedMap1404swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1404
#print axioms sourceMap1404swap_checked
#print axioms fusedMap1404swap_checked
#print axioms certified1404swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
