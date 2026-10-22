/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1217 : Family 9 := level9.get ⟨116,by decide⟩
def sourceMap1217 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1217 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1217_checked : acceptsGraphIso
    (source (graph core1217) (root 9) 0 2) DegreeTwoThreeSpectrum1886.graph sourceMap1217=true := by decide +kernel
theorem fusedMap1217_checked : acceptsGraphIso
    (fused (graph core1217) (root 9) 0 2) DegreeTwoThreeSpectrum1917.graph fusedMap1217=true := by decide +kernel
theorem certified1217 : Certified (graph core1217) (root 9) 0 2 :=
  of_native_maps core1217 DegreeTwoThreeSpectrum1886.graph DegreeTwoThreeSpectrum1917.graph
    sourceMap1217 fusedMap1217 sourceMap1217_checked fusedMap1217_checked
    DegreeTwoThreeFiniteComparisons.comparison1217
#print axioms sourceMap1217_checked
#print axioms fusedMap1217_checked
#print axioms certified1217
def sourceMap1217swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1217swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1217swap_checked : acceptsGraphIso
    (source (graph core1217) (root 9) 2 0) DegreeTwoThreeSpectrum1886.graph sourceMap1217swap=true := by decide +kernel
theorem fusedMap1217swap_checked : acceptsGraphIso
    (fused (graph core1217) (root 9) 2 0) DegreeTwoThreeSpectrum1917.graph fusedMap1217swap=true := by decide +kernel
theorem certified1217swap : Certified (graph core1217) (root 9) 2 0 :=
  of_native_maps core1217 DegreeTwoThreeSpectrum1886.graph DegreeTwoThreeSpectrum1917.graph
    sourceMap1217swap fusedMap1217swap sourceMap1217swap_checked fusedMap1217swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1217
#print axioms sourceMap1217swap_checked
#print axioms fusedMap1217swap_checked
#print axioms certified1217swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
