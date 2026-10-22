/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1262 : Family 9 := level9.get ⟨253,by decide⟩
def sourceMap1262 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1262 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1262_checked : acceptsGraphIso
    (source (graph core1262) (root 9) 0 2) DegreeTwoThreeSpectrum2188.graph sourceMap1262=true := by decide +kernel
theorem fusedMap1262_checked : acceptsGraphIso
    (fused (graph core1262) (root 9) 0 2) DegreeTwoThreeSpectrum1860.graph fusedMap1262=true := by decide +kernel
theorem certified1262 : Certified (graph core1262) (root 9) 0 2 :=
  of_native_maps core1262 DegreeTwoThreeSpectrum2188.graph DegreeTwoThreeSpectrum1860.graph
    sourceMap1262 fusedMap1262 sourceMap1262_checked fusedMap1262_checked
    DegreeTwoThreeFiniteComparisons.comparison1262
#print axioms sourceMap1262_checked
#print axioms fusedMap1262_checked
#print axioms certified1262
def sourceMap1262swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1262swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1262swap_checked : acceptsGraphIso
    (source (graph core1262) (root 9) 2 0) DegreeTwoThreeSpectrum2188.graph sourceMap1262swap=true := by decide +kernel
theorem fusedMap1262swap_checked : acceptsGraphIso
    (fused (graph core1262) (root 9) 2 0) DegreeTwoThreeSpectrum1860.graph fusedMap1262swap=true := by decide +kernel
theorem certified1262swap : Certified (graph core1262) (root 9) 2 0 :=
  of_native_maps core1262 DegreeTwoThreeSpectrum2188.graph DegreeTwoThreeSpectrum1860.graph
    sourceMap1262swap fusedMap1262swap sourceMap1262swap_checked fusedMap1262swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1262
#print axioms sourceMap1262swap_checked
#print axioms fusedMap1262swap_checked
#print axioms certified1262swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
