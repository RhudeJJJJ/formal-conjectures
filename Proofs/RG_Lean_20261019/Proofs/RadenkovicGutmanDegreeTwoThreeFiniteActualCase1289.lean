/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1289 : Family 9 := level9.get ⟨327,by decide⟩
def sourceMap1289 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1289 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1289_checked : acceptsGraphIso
    (source (graph core1289) (root 9) 0 2) DegreeTwoThreeSpectrum1943.graph sourceMap1289=true := by decide +kernel
theorem fusedMap1289_checked : acceptsGraphIso
    (fused (graph core1289) (root 9) 0 2) DegreeTwoThreeSpectrum1944.graph fusedMap1289=true := by decide +kernel
theorem certified1289 : Certified (graph core1289) (root 9) 0 2 :=
  of_native_maps core1289 DegreeTwoThreeSpectrum1943.graph DegreeTwoThreeSpectrum1944.graph
    sourceMap1289 fusedMap1289 sourceMap1289_checked fusedMap1289_checked
    DegreeTwoThreeFiniteComparisons.comparison1289
#print axioms sourceMap1289_checked
#print axioms fusedMap1289_checked
#print axioms certified1289
def sourceMap1289swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1289swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1289swap_checked : acceptsGraphIso
    (source (graph core1289) (root 9) 2 0) DegreeTwoThreeSpectrum1943.graph sourceMap1289swap=true := by decide +kernel
theorem fusedMap1289swap_checked : acceptsGraphIso
    (fused (graph core1289) (root 9) 2 0) DegreeTwoThreeSpectrum1944.graph fusedMap1289swap=true := by decide +kernel
theorem certified1289swap : Certified (graph core1289) (root 9) 2 0 :=
  of_native_maps core1289 DegreeTwoThreeSpectrum1943.graph DegreeTwoThreeSpectrum1944.graph
    sourceMap1289swap fusedMap1289swap sourceMap1289swap_checked fusedMap1289swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1289
#print axioms sourceMap1289swap_checked
#print axioms fusedMap1289swap_checked
#print axioms certified1289swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
