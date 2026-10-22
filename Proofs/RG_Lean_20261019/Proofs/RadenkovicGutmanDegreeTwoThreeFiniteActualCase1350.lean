/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1350 : Family 9 := level9.get ⟨478,by decide⟩
def sourceMap1350 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,8,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1350 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 0 2 v)
theorem sourceMap1350_checked : acceptsGraphIso
    (source (graph core1350) (root 9) 0 2) DegreeTwoThreeSpectrum2040.graph sourceMap1350=true := by decide +kernel
theorem fusedMap1350_checked : acceptsGraphIso
    (fused (graph core1350) (root 9) 0 2) DegreeTwoThreeSpectrum2175.graph fusedMap1350=true := by decide +kernel
theorem certified1350 : Certified (graph core1350) (root 9) 0 2 :=
  of_native_maps core1350 DegreeTwoThreeSpectrum2040.graph DegreeTwoThreeSpectrum2175.graph
    sourceMap1350 fusedMap1350 sourceMap1350_checked fusedMap1350_checked
    DegreeTwoThreeFiniteComparisons.comparison1350
#print axioms sourceMap1350_checked
#print axioms fusedMap1350_checked
#print axioms certified1350
def sourceMap1350swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,5,6,7,8] (sourceLabel 9 2 0 v)
def fusedMap1350swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 2 0 v)
theorem sourceMap1350swap_checked : acceptsGraphIso
    (source (graph core1350) (root 9) 2 0) DegreeTwoThreeSpectrum2040.graph sourceMap1350swap=true := by decide +kernel
theorem fusedMap1350swap_checked : acceptsGraphIso
    (fused (graph core1350) (root 9) 2 0) DegreeTwoThreeSpectrum2175.graph fusedMap1350swap=true := by decide +kernel
theorem certified1350swap : Certified (graph core1350) (root 9) 2 0 :=
  of_native_maps core1350 DegreeTwoThreeSpectrum2040.graph DegreeTwoThreeSpectrum2175.graph
    sourceMap1350swap fusedMap1350swap sourceMap1350swap_checked fusedMap1350swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1350
#print axioms sourceMap1350swap_checked
#print axioms fusedMap1350swap_checked
#print axioms certified1350swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
