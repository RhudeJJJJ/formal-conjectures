/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1298 : Family 9 := level9.get ⟨350,by decide⟩
def sourceMap1298 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1298 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1298_checked : acceptsGraphIso
    (source (graph core1298) (root 9) 0 2) DegreeTwoThreeSpectrum1981.graph sourceMap1298=true := by decide +kernel
theorem fusedMap1298_checked : acceptsGraphIso
    (fused (graph core1298) (root 9) 0 2) DegreeTwoThreeSpectrum1985.graph fusedMap1298=true := by decide +kernel
theorem certified1298 : Certified (graph core1298) (root 9) 0 2 :=
  of_native_maps core1298 DegreeTwoThreeSpectrum1981.graph DegreeTwoThreeSpectrum1985.graph
    sourceMap1298 fusedMap1298 sourceMap1298_checked fusedMap1298_checked
    DegreeTwoThreeFiniteComparisons.comparison1298
#print axioms sourceMap1298_checked
#print axioms fusedMap1298_checked
#print axioms certified1298
def sourceMap1298swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1298swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1298swap_checked : acceptsGraphIso
    (source (graph core1298) (root 9) 2 0) DegreeTwoThreeSpectrum1981.graph sourceMap1298swap=true := by decide +kernel
theorem fusedMap1298swap_checked : acceptsGraphIso
    (fused (graph core1298) (root 9) 2 0) DegreeTwoThreeSpectrum1985.graph fusedMap1298swap=true := by decide +kernel
theorem certified1298swap : Certified (graph core1298) (root 9) 2 0 :=
  of_native_maps core1298 DegreeTwoThreeSpectrum1981.graph DegreeTwoThreeSpectrum1985.graph
    sourceMap1298swap fusedMap1298swap sourceMap1298swap_checked fusedMap1298swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1298
#print axioms sourceMap1298swap_checked
#print axioms fusedMap1298swap_checked
#print axioms certified1298swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
