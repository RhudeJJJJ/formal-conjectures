/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1425 : Family 9 := level9.get ⟨667,by decide⟩
def sourceMap1425 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1425 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1425_checked : acceptsGraphIso
    (source (graph core1425) (root 9) 0 2) DegreeTwoThreeSpectrum2304.graph sourceMap1425=true := by decide +kernel
theorem fusedMap1425_checked : acceptsGraphIso
    (fused (graph core1425) (root 9) 0 2) DegreeTwoThreeSpectrum2146.graph fusedMap1425=true := by decide +kernel
theorem certified1425 : Certified (graph core1425) (root 9) 0 2 :=
  of_native_maps core1425 DegreeTwoThreeSpectrum2304.graph DegreeTwoThreeSpectrum2146.graph
    sourceMap1425 fusedMap1425 sourceMap1425_checked fusedMap1425_checked
    DegreeTwoThreeFiniteComparisons.comparison1425
#print axioms sourceMap1425_checked
#print axioms fusedMap1425_checked
#print axioms certified1425
def sourceMap1425swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,5,6,7,13] (sourceLabel 9 2 0 v)
def fusedMap1425swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1425swap_checked : acceptsGraphIso
    (source (graph core1425) (root 9) 2 0) DegreeTwoThreeSpectrum2304.graph sourceMap1425swap=true := by decide +kernel
theorem fusedMap1425swap_checked : acceptsGraphIso
    (fused (graph core1425) (root 9) 2 0) DegreeTwoThreeSpectrum2146.graph fusedMap1425swap=true := by decide +kernel
theorem certified1425swap : Certified (graph core1425) (root 9) 2 0 :=
  of_native_maps core1425 DegreeTwoThreeSpectrum2304.graph DegreeTwoThreeSpectrum2146.graph
    sourceMap1425swap fusedMap1425swap sourceMap1425swap_checked fusedMap1425swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1425
#print axioms sourceMap1425swap_checked
#print axioms fusedMap1425swap_checked
#print axioms certified1425swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
