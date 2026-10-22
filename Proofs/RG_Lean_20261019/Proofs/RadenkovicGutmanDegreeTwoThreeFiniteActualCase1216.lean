/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1216 : Family 9 := level9.get ⟨110,by decide⟩
def sourceMap1216 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,7,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1216 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1216_checked : acceptsGraphIso
    (source (graph core1216) (root 9) 0 2) DegreeTwoThreeSpectrum1868.graph sourceMap1216=true := by decide +kernel
theorem fusedMap1216_checked : acceptsGraphIso
    (fused (graph core1216) (root 9) 0 2) DegreeTwoThreeSpectrum1899.graph fusedMap1216=true := by decide +kernel
theorem certified1216 : Certified (graph core1216) (root 9) 0 2 :=
  of_native_maps core1216 DegreeTwoThreeSpectrum1868.graph DegreeTwoThreeSpectrum1899.graph
    sourceMap1216 fusedMap1216 sourceMap1216_checked fusedMap1216_checked
    DegreeTwoThreeFiniteComparisons.comparison1216
#print axioms sourceMap1216_checked
#print axioms fusedMap1216_checked
#print axioms certified1216
def sourceMap1216swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,2,3,4,7] (sourceLabel 9 2 0 v)
def fusedMap1216swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1216swap_checked : acceptsGraphIso
    (source (graph core1216) (root 9) 2 0) DegreeTwoThreeSpectrum1868.graph sourceMap1216swap=true := by decide +kernel
theorem fusedMap1216swap_checked : acceptsGraphIso
    (fused (graph core1216) (root 9) 2 0) DegreeTwoThreeSpectrum1899.graph fusedMap1216swap=true := by decide +kernel
theorem certified1216swap : Certified (graph core1216) (root 9) 2 0 :=
  of_native_maps core1216 DegreeTwoThreeSpectrum1868.graph DegreeTwoThreeSpectrum1899.graph
    sourceMap1216swap fusedMap1216swap sourceMap1216swap_checked fusedMap1216swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1216
#print axioms sourceMap1216swap_checked
#print axioms fusedMap1216swap_checked
#print axioms certified1216swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
