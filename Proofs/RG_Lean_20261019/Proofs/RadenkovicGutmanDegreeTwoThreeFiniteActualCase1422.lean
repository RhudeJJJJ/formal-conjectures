/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1422 : Family 9 := level9.get ⟨654,by decide⟩
def sourceMap1422 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1422 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1422_checked : acceptsGraphIso
    (source (graph core1422) (root 9) 0 2) DegreeTwoThreeSpectrum2298.graph sourceMap1422=true := by decide +kernel
theorem fusedMap1422_checked : acceptsGraphIso
    (fused (graph core1422) (root 9) 0 2) DegreeTwoThreeSpectrum2117.graph fusedMap1422=true := by decide +kernel
theorem certified1422 : Certified (graph core1422) (root 9) 0 2 :=
  of_native_maps core1422 DegreeTwoThreeSpectrum2298.graph DegreeTwoThreeSpectrum2117.graph
    sourceMap1422 fusedMap1422 sourceMap1422_checked fusedMap1422_checked
    DegreeTwoThreeFiniteComparisons.comparison1422
#print axioms sourceMap1422_checked
#print axioms fusedMap1422_checked
#print axioms certified1422
def sourceMap1422swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1422swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1422swap_checked : acceptsGraphIso
    (source (graph core1422) (root 9) 2 0) DegreeTwoThreeSpectrum2298.graph sourceMap1422swap=true := by decide +kernel
theorem fusedMap1422swap_checked : acceptsGraphIso
    (fused (graph core1422) (root 9) 2 0) DegreeTwoThreeSpectrum2117.graph fusedMap1422swap=true := by decide +kernel
theorem certified1422swap : Certified (graph core1422) (root 9) 2 0 :=
  of_native_maps core1422 DegreeTwoThreeSpectrum2298.graph DegreeTwoThreeSpectrum2117.graph
    sourceMap1422swap fusedMap1422swap sourceMap1422swap_checked fusedMap1422swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1422
#print axioms sourceMap1422swap_checked
#print axioms fusedMap1422swap_checked
#print axioms certified1422swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
