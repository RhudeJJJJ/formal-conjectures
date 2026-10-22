/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1679 : Family 10 := level10.get ⟨822,by decide⟩
def sourceMap1679 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1679 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1679_checked : acceptsGraphIso
    (source (graph core1679) (root 10) 0 2) DegreeTwoThreeSpectrum3294.graph sourceMap1679=true := by decide +kernel
theorem fusedMap1679_checked : acceptsGraphIso
    (fused (graph core1679) (root 10) 0 2) DegreeTwoThreeSpectrum2805.graph fusedMap1679=true := by decide +kernel
theorem certified1679 : Certified (graph core1679) (root 10) 0 2 :=
  of_native_maps core1679 DegreeTwoThreeSpectrum3294.graph DegreeTwoThreeSpectrum2805.graph
    sourceMap1679 fusedMap1679 sourceMap1679_checked fusedMap1679_checked
    DegreeTwoThreeFiniteComparisons.comparison1679
#print axioms sourceMap1679_checked
#print axioms fusedMap1679_checked
#print axioms certified1679
def sourceMap1679swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1679swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1679swap_checked : acceptsGraphIso
    (source (graph core1679) (root 10) 2 0) DegreeTwoThreeSpectrum3294.graph sourceMap1679swap=true := by decide +kernel
theorem fusedMap1679swap_checked : acceptsGraphIso
    (fused (graph core1679) (root 10) 2 0) DegreeTwoThreeSpectrum2805.graph fusedMap1679swap=true := by decide +kernel
theorem certified1679swap : Certified (graph core1679) (root 10) 2 0 :=
  of_native_maps core1679 DegreeTwoThreeSpectrum3294.graph DegreeTwoThreeSpectrum2805.graph
    sourceMap1679swap fusedMap1679swap sourceMap1679swap_checked fusedMap1679swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1679
#print axioms sourceMap1679swap_checked
#print axioms fusedMap1679swap_checked
#print axioms certified1679swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
