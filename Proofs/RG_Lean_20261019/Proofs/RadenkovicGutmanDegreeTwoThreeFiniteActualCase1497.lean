/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1497 : Family 10 := level10.get ⟨278,by decide⟩
def sourceMap1497 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,14,11,12,13,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1497 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,12,13,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1497_checked : acceptsGraphIso
    (source (graph core1497) (root 10) 0 2) DegreeTwoThreeSpectrum2629.graph sourceMap1497=true := by decide +kernel
theorem fusedMap1497_checked : acceptsGraphIso
    (fused (graph core1497) (root 10) 0 2) DegreeTwoThreeSpectrum2642.graph fusedMap1497=true := by decide +kernel
theorem certified1497 : Certified (graph core1497) (root 10) 0 2 :=
  of_native_maps core1497 DegreeTwoThreeSpectrum2629.graph DegreeTwoThreeSpectrum2642.graph
    sourceMap1497 fusedMap1497 sourceMap1497_checked fusedMap1497_checked
    DegreeTwoThreeFiniteComparisons.comparison1497
#print axioms sourceMap1497_checked
#print axioms fusedMap1497_checked
#print axioms certified1497
def sourceMap1497swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,14,11,12,8,9,10,13] (sourceLabel 10 2 0 v)
def fusedMap1497swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,12,13,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1497swap_checked : acceptsGraphIso
    (source (graph core1497) (root 10) 2 0) DegreeTwoThreeSpectrum2629.graph sourceMap1497swap=true := by decide +kernel
theorem fusedMap1497swap_checked : acceptsGraphIso
    (fused (graph core1497) (root 10) 2 0) DegreeTwoThreeSpectrum2642.graph fusedMap1497swap=true := by decide +kernel
theorem certified1497swap : Certified (graph core1497) (root 10) 2 0 :=
  of_native_maps core1497 DegreeTwoThreeSpectrum2629.graph DegreeTwoThreeSpectrum2642.graph
    sourceMap1497swap fusedMap1497swap sourceMap1497swap_checked fusedMap1497swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1497
#print axioms sourceMap1497swap_checked
#print axioms fusedMap1497swap_checked
#print axioms certified1497swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
