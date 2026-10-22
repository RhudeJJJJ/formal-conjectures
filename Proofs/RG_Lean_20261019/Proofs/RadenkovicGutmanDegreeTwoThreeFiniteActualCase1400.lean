/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1400 : Family 9 := level9.get ⟨597,by decide⟩
def sourceMap1400 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1400 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1400_checked : acceptsGraphIso
    (source (graph core1400) (root 9) 0 2) DegreeTwoThreeSpectrum2272.graph sourceMap1400=true := by decide +kernel
theorem fusedMap1400_checked : acceptsGraphIso
    (fused (graph core1400) (root 9) 0 2) DegreeTwoThreeSpectrum2000.graph fusedMap1400=true := by decide +kernel
theorem certified1400 : Certified (graph core1400) (root 9) 0 2 :=
  of_native_maps core1400 DegreeTwoThreeSpectrum2272.graph DegreeTwoThreeSpectrum2000.graph
    sourceMap1400 fusedMap1400 sourceMap1400_checked fusedMap1400_checked
    DegreeTwoThreeFiniteComparisons.comparison1400
#print axioms sourceMap1400_checked
#print axioms fusedMap1400_checked
#print axioms certified1400
def sourceMap1400swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1400swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1400swap_checked : acceptsGraphIso
    (source (graph core1400) (root 9) 2 0) DegreeTwoThreeSpectrum2272.graph sourceMap1400swap=true := by decide +kernel
theorem fusedMap1400swap_checked : acceptsGraphIso
    (fused (graph core1400) (root 9) 2 0) DegreeTwoThreeSpectrum2000.graph fusedMap1400swap=true := by decide +kernel
theorem certified1400swap : Certified (graph core1400) (root 9) 2 0 :=
  of_native_maps core1400 DegreeTwoThreeSpectrum2272.graph DegreeTwoThreeSpectrum2000.graph
    sourceMap1400swap fusedMap1400swap sourceMap1400swap_checked fusedMap1400swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1400
#print axioms sourceMap1400swap_checked
#print axioms fusedMap1400swap_checked
#print axioms certified1400swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
