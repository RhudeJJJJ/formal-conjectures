/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1415 : Family 9 := level9.get ⟨638,by decide⟩
def sourceMap1415 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1415 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1415_checked : acceptsGraphIso
    (source (graph core1415) (root 9) 0 2) DegreeTwoThreeSpectrum2290.graph sourceMap1415=true := by decide +kernel
theorem fusedMap1415_checked : acceptsGraphIso
    (fused (graph core1415) (root 9) 0 2) DegreeTwoThreeSpectrum2087.graph fusedMap1415=true := by decide +kernel
theorem certified1415 : Certified (graph core1415) (root 9) 0 2 :=
  of_native_maps core1415 DegreeTwoThreeSpectrum2290.graph DegreeTwoThreeSpectrum2087.graph
    sourceMap1415 fusedMap1415 sourceMap1415_checked fusedMap1415_checked
    DegreeTwoThreeFiniteComparisons.comparison1415
#print axioms sourceMap1415_checked
#print axioms fusedMap1415_checked
#print axioms certified1415
def sourceMap1415swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1415swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1415swap_checked : acceptsGraphIso
    (source (graph core1415) (root 9) 2 0) DegreeTwoThreeSpectrum2290.graph sourceMap1415swap=true := by decide +kernel
theorem fusedMap1415swap_checked : acceptsGraphIso
    (fused (graph core1415) (root 9) 2 0) DegreeTwoThreeSpectrum2087.graph fusedMap1415swap=true := by decide +kernel
theorem certified1415swap : Certified (graph core1415) (root 9) 2 0 :=
  of_native_maps core1415 DegreeTwoThreeSpectrum2290.graph DegreeTwoThreeSpectrum2087.graph
    sourceMap1415swap fusedMap1415swap sourceMap1415swap_checked fusedMap1415swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1415
#print axioms sourceMap1415swap_checked
#print axioms fusedMap1415swap_checked
#print axioms certified1415swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
