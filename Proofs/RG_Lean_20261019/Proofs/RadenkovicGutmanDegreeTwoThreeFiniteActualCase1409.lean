/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1409 : Family 9 := level9.get ⟨618,by decide⟩
def sourceMap1409 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1409 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1409_checked : acceptsGraphIso
    (source (graph core1409) (root 9) 0 2) DegreeTwoThreeSpectrum2282.graph sourceMap1409=true := by decide +kernel
theorem fusedMap1409_checked : acceptsGraphIso
    (fused (graph core1409) (root 9) 0 2) DegreeTwoThreeSpectrum2038.graph fusedMap1409=true := by decide +kernel
theorem certified1409 : Certified (graph core1409) (root 9) 0 2 :=
  of_native_maps core1409 DegreeTwoThreeSpectrum2282.graph DegreeTwoThreeSpectrum2038.graph
    sourceMap1409 fusedMap1409 sourceMap1409_checked fusedMap1409_checked
    DegreeTwoThreeFiniteComparisons.comparison1409
#print axioms sourceMap1409_checked
#print axioms fusedMap1409_checked
#print axioms certified1409
def sourceMap1409swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1409swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1409swap_checked : acceptsGraphIso
    (source (graph core1409) (root 9) 2 0) DegreeTwoThreeSpectrum2282.graph sourceMap1409swap=true := by decide +kernel
theorem fusedMap1409swap_checked : acceptsGraphIso
    (fused (graph core1409) (root 9) 2 0) DegreeTwoThreeSpectrum2038.graph fusedMap1409swap=true := by decide +kernel
theorem certified1409swap : Certified (graph core1409) (root 9) 2 0 :=
  of_native_maps core1409 DegreeTwoThreeSpectrum2282.graph DegreeTwoThreeSpectrum2038.graph
    sourceMap1409swap fusedMap1409swap sourceMap1409swap_checked fusedMap1409swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1409
#print axioms sourceMap1409swap_checked
#print axioms fusedMap1409swap_checked
#print axioms certified1409swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
