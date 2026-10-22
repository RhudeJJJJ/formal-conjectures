/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3289 : Family 9 := level9.get ⟨203,by decide⟩
def sourceMap3289 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3289 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3289_checked : acceptsGraphIso
    (source (graph core3289) (root 9) 0 5) DegreeTwoThreeSpectrum5437.graph sourceMap3289=true := by decide +kernel
theorem fusedMap3289_checked : acceptsGraphIso
    (fused (graph core3289) (root 9) 0 5) DegreeTwoThreeSpectrum5438.graph fusedMap3289=true := by decide +kernel
theorem certified3289 : Certified (graph core3289) (root 9) 0 5 :=
  of_native_maps core3289 DegreeTwoThreeSpectrum5437.graph DegreeTwoThreeSpectrum5438.graph
    sourceMap3289 fusedMap3289 sourceMap3289_checked fusedMap3289_checked
    DegreeTwoThreeFiniteComparisons.comparison3289
#print axioms sourceMap3289_checked
#print axioms fusedMap3289_checked
#print axioms certified3289
def sourceMap3289swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3289swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3289swap_checked : acceptsGraphIso
    (source (graph core3289) (root 9) 5 0) DegreeTwoThreeSpectrum5437.graph sourceMap3289swap=true := by decide +kernel
theorem fusedMap3289swap_checked : acceptsGraphIso
    (fused (graph core3289) (root 9) 5 0) DegreeTwoThreeSpectrum5438.graph fusedMap3289swap=true := by decide +kernel
theorem certified3289swap : Certified (graph core3289) (root 9) 5 0 :=
  of_native_maps core3289 DegreeTwoThreeSpectrum5437.graph DegreeTwoThreeSpectrum5438.graph
    sourceMap3289swap fusedMap3289swap sourceMap3289swap_checked fusedMap3289swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3289
#print axioms sourceMap3289swap_checked
#print axioms fusedMap3289swap_checked
#print axioms certified3289swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
