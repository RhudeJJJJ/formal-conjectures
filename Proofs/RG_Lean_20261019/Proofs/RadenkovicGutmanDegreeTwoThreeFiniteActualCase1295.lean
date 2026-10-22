/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1295 : Family 9 := level9.get ⟨345,by decide⟩
def sourceMap1295 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1295 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1295_checked : acceptsGraphIso
    (source (graph core1295) (root 9) 0 2) DegreeTwoThreeSpectrum1974.graph sourceMap1295=true := by decide +kernel
theorem fusedMap1295_checked : acceptsGraphIso
    (fused (graph core1295) (root 9) 0 2) DegreeTwoThreeSpectrum1975.graph fusedMap1295=true := by decide +kernel
theorem certified1295 : Certified (graph core1295) (root 9) 0 2 :=
  of_native_maps core1295 DegreeTwoThreeSpectrum1974.graph DegreeTwoThreeSpectrum1975.graph
    sourceMap1295 fusedMap1295 sourceMap1295_checked fusedMap1295_checked
    DegreeTwoThreeFiniteComparisons.comparison1295
#print axioms sourceMap1295_checked
#print axioms fusedMap1295_checked
#print axioms certified1295
def sourceMap1295swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1295swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1295swap_checked : acceptsGraphIso
    (source (graph core1295) (root 9) 2 0) DegreeTwoThreeSpectrum1974.graph sourceMap1295swap=true := by decide +kernel
theorem fusedMap1295swap_checked : acceptsGraphIso
    (fused (graph core1295) (root 9) 2 0) DegreeTwoThreeSpectrum1975.graph fusedMap1295swap=true := by decide +kernel
theorem certified1295swap : Certified (graph core1295) (root 9) 2 0 :=
  of_native_maps core1295 DegreeTwoThreeSpectrum1974.graph DegreeTwoThreeSpectrum1975.graph
    sourceMap1295swap fusedMap1295swap sourceMap1295swap_checked fusedMap1295swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1295
#print axioms sourceMap1295swap_checked
#print axioms fusedMap1295swap_checked
#print axioms certified1295swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
