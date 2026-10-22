/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1426 : Family 9 := level9.get ⟨678,by decide⟩
def sourceMap1426 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,7,8,9,10,11,12,13,4,5,6] (sourceLabel 9 0 2 v)
def fusedMap1426 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1426_checked : acceptsGraphIso
    (source (graph core1426) (root 9) 0 2) DegreeTwoThreeSpectrum2306.graph sourceMap1426=true := by decide +kernel
theorem fusedMap1426_checked : acceptsGraphIso
    (fused (graph core1426) (root 9) 0 2) DegreeTwoThreeSpectrum2190.graph fusedMap1426=true := by decide +kernel
theorem certified1426 : Certified (graph core1426) (root 9) 0 2 :=
  of_native_maps core1426 DegreeTwoThreeSpectrum2306.graph DegreeTwoThreeSpectrum2190.graph
    sourceMap1426 fusedMap1426 sourceMap1426_checked fusedMap1426_checked
    DegreeTwoThreeFiniteComparisons.comparison1426
#print axioms sourceMap1426_checked
#print axioms fusedMap1426_checked
#print axioms certified1426
def sourceMap1426swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,7,8,9,10,11,12,4,5,6,13] (sourceLabel 9 2 0 v)
def fusedMap1426swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1426swap_checked : acceptsGraphIso
    (source (graph core1426) (root 9) 2 0) DegreeTwoThreeSpectrum2306.graph sourceMap1426swap=true := by decide +kernel
theorem fusedMap1426swap_checked : acceptsGraphIso
    (fused (graph core1426) (root 9) 2 0) DegreeTwoThreeSpectrum2190.graph fusedMap1426swap=true := by decide +kernel
theorem certified1426swap : Certified (graph core1426) (root 9) 2 0 :=
  of_native_maps core1426 DegreeTwoThreeSpectrum2306.graph DegreeTwoThreeSpectrum2190.graph
    sourceMap1426swap fusedMap1426swap sourceMap1426swap_checked fusedMap1426swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1426
#print axioms sourceMap1426swap_checked
#print axioms fusedMap1426swap_checked
#print axioms certified1426swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
