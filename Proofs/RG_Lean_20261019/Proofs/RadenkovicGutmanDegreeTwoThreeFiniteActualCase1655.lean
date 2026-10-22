/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1655 : Family 10 := level10.get ⟨759,by decide⟩
def sourceMap1655 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1655 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1655_checked : acceptsGraphIso
    (source (graph core1655) (root 10) 0 2) DegreeTwoThreeSpectrum3517.graph sourceMap1655=true := by decide +kernel
theorem fusedMap1655_checked : acceptsGraphIso
    (fused (graph core1655) (root 10) 0 2) DegreeTwoThreeSpectrum2726.graph fusedMap1655=true := by decide +kernel
theorem certified1655 : Certified (graph core1655) (root 10) 0 2 :=
  of_native_maps core1655 DegreeTwoThreeSpectrum3517.graph DegreeTwoThreeSpectrum2726.graph
    sourceMap1655 fusedMap1655 sourceMap1655_checked fusedMap1655_checked
    DegreeTwoThreeFiniteComparisons.comparison1655
#print axioms sourceMap1655_checked
#print axioms fusedMap1655_checked
#print axioms certified1655
def sourceMap1655swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1655swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1655swap_checked : acceptsGraphIso
    (source (graph core1655) (root 10) 2 0) DegreeTwoThreeSpectrum3517.graph sourceMap1655swap=true := by decide +kernel
theorem fusedMap1655swap_checked : acceptsGraphIso
    (fused (graph core1655) (root 10) 2 0) DegreeTwoThreeSpectrum2726.graph fusedMap1655swap=true := by decide +kernel
theorem certified1655swap : Certified (graph core1655) (root 10) 2 0 :=
  of_native_maps core1655 DegreeTwoThreeSpectrum3517.graph DegreeTwoThreeSpectrum2726.graph
    sourceMap1655swap fusedMap1655swap sourceMap1655swap_checked fusedMap1655swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1655
#print axioms sourceMap1655swap_checked
#print axioms fusedMap1655swap_checked
#print axioms certified1655swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
