/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1201 : Family 9 := level9.get ⟨54,by decide⟩
def sourceMap1201 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1201 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1201_checked : acceptsGraphIso
    (source (graph core1201) (root 9) 0 2) DegreeTwoThreeSpectrum1772.graph sourceMap1201=true := by decide +kernel
theorem fusedMap1201_checked : acceptsGraphIso
    (fused (graph core1201) (root 9) 0 2) DegreeTwoThreeSpectrum1774.graph fusedMap1201=true := by decide +kernel
theorem certified1201 : Certified (graph core1201) (root 9) 0 2 :=
  of_native_maps core1201 DegreeTwoThreeSpectrum1772.graph DegreeTwoThreeSpectrum1774.graph
    sourceMap1201 fusedMap1201 sourceMap1201_checked fusedMap1201_checked
    DegreeTwoThreeFiniteComparisons.comparison1201
#print axioms sourceMap1201_checked
#print axioms fusedMap1201_checked
#print axioms certified1201
def sourceMap1201swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1201swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1201swap_checked : acceptsGraphIso
    (source (graph core1201) (root 9) 2 0) DegreeTwoThreeSpectrum1772.graph sourceMap1201swap=true := by decide +kernel
theorem fusedMap1201swap_checked : acceptsGraphIso
    (fused (graph core1201) (root 9) 2 0) DegreeTwoThreeSpectrum1774.graph fusedMap1201swap=true := by decide +kernel
theorem certified1201swap : Certified (graph core1201) (root 9) 2 0 :=
  of_native_maps core1201 DegreeTwoThreeSpectrum1772.graph DegreeTwoThreeSpectrum1774.graph
    sourceMap1201swap fusedMap1201swap sourceMap1201swap_checked fusedMap1201swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1201
#print axioms sourceMap1201swap_checked
#print axioms fusedMap1201swap_checked
#print axioms certified1201swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
