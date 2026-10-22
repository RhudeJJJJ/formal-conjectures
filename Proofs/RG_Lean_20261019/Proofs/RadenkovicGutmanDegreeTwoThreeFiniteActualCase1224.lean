/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1224 : Family 9 := level9.get ⟨133,by decide⟩
def sourceMap1224 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,2,3,4,8,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1224 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,6,7,8,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1224_checked : acceptsGraphIso
    (source (graph core1224) (root 9) 0 2) DegreeTwoThreeSpectrum1859.graph sourceMap1224=true := by decide +kernel
theorem fusedMap1224_checked : acceptsGraphIso
    (fused (graph core1224) (root 9) 0 2) DegreeTwoThreeSpectrum1907.graph fusedMap1224=true := by decide +kernel
theorem certified1224 : Certified (graph core1224) (root 9) 0 2 :=
  of_native_maps core1224 DegreeTwoThreeSpectrum1859.graph DegreeTwoThreeSpectrum1907.graph
    sourceMap1224 fusedMap1224 sourceMap1224_checked fusedMap1224_checked
    DegreeTwoThreeFiniteComparisons.comparison1224
#print axioms sourceMap1224_checked
#print axioms fusedMap1224_checked
#print axioms certified1224
def sourceMap1224swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,2,3,4,5,6,7,8] (sourceLabel 9 2 0 v)
def fusedMap1224swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,6,7,8,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1224swap_checked : acceptsGraphIso
    (source (graph core1224) (root 9) 2 0) DegreeTwoThreeSpectrum1859.graph sourceMap1224swap=true := by decide +kernel
theorem fusedMap1224swap_checked : acceptsGraphIso
    (fused (graph core1224) (root 9) 2 0) DegreeTwoThreeSpectrum1907.graph fusedMap1224swap=true := by decide +kernel
theorem certified1224swap : Certified (graph core1224) (root 9) 2 0 :=
  of_native_maps core1224 DegreeTwoThreeSpectrum1859.graph DegreeTwoThreeSpectrum1907.graph
    sourceMap1224swap fusedMap1224swap sourceMap1224swap_checked fusedMap1224swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1224
#print axioms sourceMap1224swap_checked
#print axioms fusedMap1224swap_checked
#print axioms certified1224swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
