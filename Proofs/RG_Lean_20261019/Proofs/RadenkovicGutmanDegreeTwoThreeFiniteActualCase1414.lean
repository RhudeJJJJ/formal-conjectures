/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1414 : Family 9 := level9.get ⟨636,by decide⟩
def sourceMap1414 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1414 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1414_checked : acceptsGraphIso
    (source (graph core1414) (root 9) 0 2) DegreeTwoThreeSpectrum2289.graph sourceMap1414=true := by decide +kernel
theorem fusedMap1414_checked : acceptsGraphIso
    (fused (graph core1414) (root 9) 0 2) DegreeTwoThreeSpectrum2084.graph fusedMap1414=true := by decide +kernel
theorem certified1414 : Certified (graph core1414) (root 9) 0 2 :=
  of_native_maps core1414 DegreeTwoThreeSpectrum2289.graph DegreeTwoThreeSpectrum2084.graph
    sourceMap1414 fusedMap1414 sourceMap1414_checked fusedMap1414_checked
    DegreeTwoThreeFiniteComparisons.comparison1414
#print axioms sourceMap1414_checked
#print axioms fusedMap1414_checked
#print axioms certified1414
def sourceMap1414swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1414swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1414swap_checked : acceptsGraphIso
    (source (graph core1414) (root 9) 2 0) DegreeTwoThreeSpectrum2289.graph sourceMap1414swap=true := by decide +kernel
theorem fusedMap1414swap_checked : acceptsGraphIso
    (fused (graph core1414) (root 9) 2 0) DegreeTwoThreeSpectrum2084.graph fusedMap1414swap=true := by decide +kernel
theorem certified1414swap : Certified (graph core1414) (root 9) 2 0 :=
  of_native_maps core1414 DegreeTwoThreeSpectrum2289.graph DegreeTwoThreeSpectrum2084.graph
    sourceMap1414swap fusedMap1414swap sourceMap1414swap_checked fusedMap1414swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1414
#print axioms sourceMap1414swap_checked
#print axioms fusedMap1414swap_checked
#print axioms certified1414swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
