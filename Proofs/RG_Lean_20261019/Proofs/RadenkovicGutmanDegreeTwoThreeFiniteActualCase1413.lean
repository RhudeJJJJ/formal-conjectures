/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1413 : Family 9 := level9.get ⟨635,by decide⟩
def sourceMap1413 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1413 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1413_checked : acceptsGraphIso
    (source (graph core1413) (root 9) 0 2) DegreeTwoThreeSpectrum2288.graph sourceMap1413=true := by decide +kernel
theorem fusedMap1413_checked : acceptsGraphIso
    (fused (graph core1413) (root 9) 0 2) DegreeTwoThreeSpectrum2083.graph fusedMap1413=true := by decide +kernel
theorem certified1413 : Certified (graph core1413) (root 9) 0 2 :=
  of_native_maps core1413 DegreeTwoThreeSpectrum2288.graph DegreeTwoThreeSpectrum2083.graph
    sourceMap1413 fusedMap1413 sourceMap1413_checked fusedMap1413_checked
    DegreeTwoThreeFiniteComparisons.comparison1413
#print axioms sourceMap1413_checked
#print axioms fusedMap1413_checked
#print axioms certified1413
def sourceMap1413swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1413swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1413swap_checked : acceptsGraphIso
    (source (graph core1413) (root 9) 2 0) DegreeTwoThreeSpectrum2288.graph sourceMap1413swap=true := by decide +kernel
theorem fusedMap1413swap_checked : acceptsGraphIso
    (fused (graph core1413) (root 9) 2 0) DegreeTwoThreeSpectrum2083.graph fusedMap1413swap=true := by decide +kernel
theorem certified1413swap : Certified (graph core1413) (root 9) 2 0 :=
  of_native_maps core1413 DegreeTwoThreeSpectrum2288.graph DegreeTwoThreeSpectrum2083.graph
    sourceMap1413swap fusedMap1413swap sourceMap1413swap_checked fusedMap1413swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1413
#print axioms sourceMap1413swap_checked
#print axioms fusedMap1413swap_checked
#print axioms certified1413swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
