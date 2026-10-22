/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1256 : Family 9 := level9.get ⟨237,by decide⟩
def sourceMap1256 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1256 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1256_checked : acceptsGraphIso
    (source (graph core1256) (root 9) 0 2) DegreeTwoThreeSpectrum2163.graph sourceMap1256=true := by decide +kernel
theorem fusedMap1256_checked : acceptsGraphIso
    (fused (graph core1256) (root 9) 0 2) DegreeTwoThreeSpectrum1841.graph fusedMap1256=true := by decide +kernel
theorem certified1256 : Certified (graph core1256) (root 9) 0 2 :=
  of_native_maps core1256 DegreeTwoThreeSpectrum2163.graph DegreeTwoThreeSpectrum1841.graph
    sourceMap1256 fusedMap1256 sourceMap1256_checked fusedMap1256_checked
    DegreeTwoThreeFiniteComparisons.comparison1256
#print axioms sourceMap1256_checked
#print axioms fusedMap1256_checked
#print axioms certified1256
def sourceMap1256swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1256swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1256swap_checked : acceptsGraphIso
    (source (graph core1256) (root 9) 2 0) DegreeTwoThreeSpectrum2163.graph sourceMap1256swap=true := by decide +kernel
theorem fusedMap1256swap_checked : acceptsGraphIso
    (fused (graph core1256) (root 9) 2 0) DegreeTwoThreeSpectrum1841.graph fusedMap1256swap=true := by decide +kernel
theorem certified1256swap : Certified (graph core1256) (root 9) 2 0 :=
  of_native_maps core1256 DegreeTwoThreeSpectrum2163.graph DegreeTwoThreeSpectrum1841.graph
    sourceMap1256swap fusedMap1256swap sourceMap1256swap_checked fusedMap1256swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1256
#print axioms sourceMap1256swap_checked
#print axioms fusedMap1256swap_checked
#print axioms certified1256swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
