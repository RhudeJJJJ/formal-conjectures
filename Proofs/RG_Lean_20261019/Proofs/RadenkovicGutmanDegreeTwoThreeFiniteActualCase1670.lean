/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1670 : Family 10 := level10.get ⟨804,by decide⟩
def sourceMap1670 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,11,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1670 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1670_checked : acceptsGraphIso
    (source (graph core1670) (root 10) 0 2) DegreeTwoThreeSpectrum3599.graph sourceMap1670=true := by decide +kernel
theorem fusedMap1670_checked : acceptsGraphIso
    (fused (graph core1670) (root 10) 0 2) DegreeTwoThreeSpectrum2773.graph fusedMap1670=true := by decide +kernel
theorem certified1670 : Certified (graph core1670) (root 10) 0 2 :=
  of_native_maps core1670 DegreeTwoThreeSpectrum3599.graph DegreeTwoThreeSpectrum2773.graph
    sourceMap1670 fusedMap1670 sourceMap1670_checked fusedMap1670_checked
    DegreeTwoThreeFiniteComparisons.comparison1670
#print axioms sourceMap1670_checked
#print axioms fusedMap1670_checked
#print axioms certified1670
def sourceMap1670swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,7,8,9,11] (sourceLabel 10 2 0 v)
def fusedMap1670swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1670swap_checked : acceptsGraphIso
    (source (graph core1670) (root 10) 2 0) DegreeTwoThreeSpectrum3599.graph sourceMap1670swap=true := by decide +kernel
theorem fusedMap1670swap_checked : acceptsGraphIso
    (fused (graph core1670) (root 10) 2 0) DegreeTwoThreeSpectrum2773.graph fusedMap1670swap=true := by decide +kernel
theorem certified1670swap : Certified (graph core1670) (root 10) 2 0 :=
  of_native_maps core1670 DegreeTwoThreeSpectrum3599.graph DegreeTwoThreeSpectrum2773.graph
    sourceMap1670swap fusedMap1670swap sourceMap1670swap_checked fusedMap1670swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1670
#print axioms sourceMap1670swap_checked
#print axioms fusedMap1670swap_checked
#print axioms certified1670swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
