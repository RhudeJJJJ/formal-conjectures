/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1280 : Family 9 := level9.get ⟨302,by decide⟩
def sourceMap1280 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,7,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1280 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,5,6,1,2,3,4] (fusedLabel 9 0 2 v)
theorem sourceMap1280_checked : acceptsGraphIso
    (source (graph core1280) (root 9) 0 2) DegreeTwoThreeSpectrum2214.graph sourceMap1280=true := by decide +kernel
theorem fusedMap1280_checked : acceptsGraphIso
    (fused (graph core1280) (root 9) 0 2) DegreeTwoThreeSpectrum1916.graph fusedMap1280=true := by decide +kernel
theorem certified1280 : Certified (graph core1280) (root 9) 0 2 :=
  of_native_maps core1280 DegreeTwoThreeSpectrum2214.graph DegreeTwoThreeSpectrum1916.graph
    sourceMap1280 fusedMap1280 sourceMap1280_checked fusedMap1280_checked
    DegreeTwoThreeFiniteComparisons.comparison1280
#print axioms sourceMap1280_checked
#print axioms fusedMap1280_checked
#print axioms certified1280
def sourceMap1280swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,2,3,4,7] (sourceLabel 9 2 0 v)
def fusedMap1280swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,5,6,1,2,3,4] (fusedLabel 9 2 0 v)
theorem sourceMap1280swap_checked : acceptsGraphIso
    (source (graph core1280) (root 9) 2 0) DegreeTwoThreeSpectrum2214.graph sourceMap1280swap=true := by decide +kernel
theorem fusedMap1280swap_checked : acceptsGraphIso
    (fused (graph core1280) (root 9) 2 0) DegreeTwoThreeSpectrum1916.graph fusedMap1280swap=true := by decide +kernel
theorem certified1280swap : Certified (graph core1280) (root 9) 2 0 :=
  of_native_maps core1280 DegreeTwoThreeSpectrum2214.graph DegreeTwoThreeSpectrum1916.graph
    sourceMap1280swap fusedMap1280swap sourceMap1280swap_checked fusedMap1280swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1280
#print axioms sourceMap1280swap_checked
#print axioms fusedMap1280swap_checked
#print axioms certified1280swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
