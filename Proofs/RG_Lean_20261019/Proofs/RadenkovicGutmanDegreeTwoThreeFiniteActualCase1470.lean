/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1470 : Family 10 := level10.get ⟨182,by decide⟩
def sourceMap1470 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,8,9,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1470 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1470_checked : acceptsGraphIso
    (source (graph core1470) (root 10) 0 2) DegreeTwoThreeSpectrum2888.graph sourceMap1470=true := by decide +kernel
theorem fusedMap1470_checked : acceptsGraphIso
    (fused (graph core1470) (root 10) 0 2) DegreeTwoThreeSpectrum2419.graph fusedMap1470=true := by decide +kernel
theorem certified1470 : Certified (graph core1470) (root 10) 0 2 :=
  of_native_maps core1470 DegreeTwoThreeSpectrum2888.graph DegreeTwoThreeSpectrum2419.graph
    sourceMap1470 fusedMap1470 sourceMap1470_checked fusedMap1470_checked
    DegreeTwoThreeFiniteComparisons.comparison1470
#print axioms sourceMap1470_checked
#print axioms fusedMap1470_checked
#print axioms certified1470
def sourceMap1470swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,8,9,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1470swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1470swap_checked : acceptsGraphIso
    (source (graph core1470) (root 10) 2 0) DegreeTwoThreeSpectrum2888.graph sourceMap1470swap=true := by decide +kernel
theorem fusedMap1470swap_checked : acceptsGraphIso
    (fused (graph core1470) (root 10) 2 0) DegreeTwoThreeSpectrum2419.graph fusedMap1470swap=true := by decide +kernel
theorem certified1470swap : Certified (graph core1470) (root 10) 2 0 :=
  of_native_maps core1470 DegreeTwoThreeSpectrum2888.graph DegreeTwoThreeSpectrum2419.graph
    sourceMap1470swap fusedMap1470swap sourceMap1470swap_checked fusedMap1470swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1470
#print axioms sourceMap1470swap_checked
#print axioms fusedMap1470swap_checked
#print axioms certified1470swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
