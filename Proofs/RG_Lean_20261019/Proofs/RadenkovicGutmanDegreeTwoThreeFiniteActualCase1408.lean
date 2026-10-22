/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1408 : Family 9 := level9.get ⟨617,by decide⟩
def sourceMap1408 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1408 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1408_checked : acceptsGraphIso
    (source (graph core1408) (root 9) 0 2) DegreeTwoThreeSpectrum2281.graph sourceMap1408=true := by decide +kernel
theorem fusedMap1408_checked : acceptsGraphIso
    (fused (graph core1408) (root 9) 0 2) DegreeTwoThreeSpectrum2037.graph fusedMap1408=true := by decide +kernel
theorem certified1408 : Certified (graph core1408) (root 9) 0 2 :=
  of_native_maps core1408 DegreeTwoThreeSpectrum2281.graph DegreeTwoThreeSpectrum2037.graph
    sourceMap1408 fusedMap1408 sourceMap1408_checked fusedMap1408_checked
    DegreeTwoThreeFiniteComparisons.comparison1408
#print axioms sourceMap1408_checked
#print axioms fusedMap1408_checked
#print axioms certified1408
def sourceMap1408swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1408swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1408swap_checked : acceptsGraphIso
    (source (graph core1408) (root 9) 2 0) DegreeTwoThreeSpectrum2281.graph sourceMap1408swap=true := by decide +kernel
theorem fusedMap1408swap_checked : acceptsGraphIso
    (fused (graph core1408) (root 9) 2 0) DegreeTwoThreeSpectrum2037.graph fusedMap1408swap=true := by decide +kernel
theorem certified1408swap : Certified (graph core1408) (root 9) 2 0 :=
  of_native_maps core1408 DegreeTwoThreeSpectrum2281.graph DegreeTwoThreeSpectrum2037.graph
    sourceMap1408swap fusedMap1408swap sourceMap1408swap_checked fusedMap1408swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1408
#print axioms sourceMap1408swap_checked
#print axioms fusedMap1408swap_checked
#print axioms certified1408swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
