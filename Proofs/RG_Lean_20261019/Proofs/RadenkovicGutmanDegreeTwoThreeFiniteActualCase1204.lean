/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1204 : Family 9 := level9.get ⟨66,by decide⟩
def sourceMap1204 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,13,11,12,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1204 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,12,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1204_checked : acceptsGraphIso
    (source (graph core1204) (root 9) 0 2) DegreeTwoThreeSpectrum1797.graph sourceMap1204=true := by decide +kernel
theorem fusedMap1204_checked : acceptsGraphIso
    (fused (graph core1204) (root 9) 0 2) DegreeTwoThreeSpectrum1802.graph fusedMap1204=true := by decide +kernel
theorem certified1204 : Certified (graph core1204) (root 9) 0 2 :=
  of_native_maps core1204 DegreeTwoThreeSpectrum1797.graph DegreeTwoThreeSpectrum1802.graph
    sourceMap1204 fusedMap1204 sourceMap1204_checked fusedMap1204_checked
    DegreeTwoThreeFiniteComparisons.comparison1204
#print axioms sourceMap1204_checked
#print axioms fusedMap1204_checked
#print axioms certified1204
def sourceMap1204swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,13,11,8,9,10,12] (sourceLabel 9 2 0 v)
def fusedMap1204swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,12,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1204swap_checked : acceptsGraphIso
    (source (graph core1204) (root 9) 2 0) DegreeTwoThreeSpectrum1797.graph sourceMap1204swap=true := by decide +kernel
theorem fusedMap1204swap_checked : acceptsGraphIso
    (fused (graph core1204) (root 9) 2 0) DegreeTwoThreeSpectrum1802.graph fusedMap1204swap=true := by decide +kernel
theorem certified1204swap : Certified (graph core1204) (root 9) 2 0 :=
  of_native_maps core1204 DegreeTwoThreeSpectrum1797.graph DegreeTwoThreeSpectrum1802.graph
    sourceMap1204swap fusedMap1204swap sourceMap1204swap_checked fusedMap1204swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1204
#print axioms sourceMap1204swap_checked
#print axioms fusedMap1204swap_checked
#print axioms certified1204swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
