/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1488 : Family 10 := level10.get ⟨253,by decide⟩
def sourceMap1488 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1488 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1488_checked : acceptsGraphIso
    (source (graph core1488) (root 10) 0 2) DegreeTwoThreeSpectrum2591.graph sourceMap1488=true := by decide +kernel
theorem fusedMap1488_checked : acceptsGraphIso
    (fused (graph core1488) (root 10) 0 2) DegreeTwoThreeSpectrum2593.graph fusedMap1488=true := by decide +kernel
theorem certified1488 : Certified (graph core1488) (root 10) 0 2 :=
  of_native_maps core1488 DegreeTwoThreeSpectrum2591.graph DegreeTwoThreeSpectrum2593.graph
    sourceMap1488 fusedMap1488 sourceMap1488_checked fusedMap1488_checked
    DegreeTwoThreeFiniteComparisons.comparison1488
#print axioms sourceMap1488_checked
#print axioms fusedMap1488_checked
#print axioms certified1488
def sourceMap1488swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1488swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1488swap_checked : acceptsGraphIso
    (source (graph core1488) (root 10) 2 0) DegreeTwoThreeSpectrum2591.graph sourceMap1488swap=true := by decide +kernel
theorem fusedMap1488swap_checked : acceptsGraphIso
    (fused (graph core1488) (root 10) 2 0) DegreeTwoThreeSpectrum2593.graph fusedMap1488swap=true := by decide +kernel
theorem certified1488swap : Certified (graph core1488) (root 10) 2 0 :=
  of_native_maps core1488 DegreeTwoThreeSpectrum2591.graph DegreeTwoThreeSpectrum2593.graph
    sourceMap1488swap fusedMap1488swap sourceMap1488swap_checked fusedMap1488swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1488
#print axioms sourceMap1488swap_checked
#print axioms fusedMap1488swap_checked
#print axioms certified1488swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
