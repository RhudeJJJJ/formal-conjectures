/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1448 : Family 10 := level10.get ⟨98,by decide⟩
def sourceMap1448 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1448 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1448_checked : acceptsGraphIso
    (source (graph core1448) (root 10) 0 2) DegreeTwoThreeSpectrum2725.graph sourceMap1448=true := by decide +kernel
theorem fusedMap1448_checked : acceptsGraphIso
    (fused (graph core1448) (root 10) 0 2) DegreeTwoThreeSpectrum2358.graph fusedMap1448=true := by decide +kernel
theorem certified1448 : Certified (graph core1448) (root 10) 0 2 :=
  of_native_maps core1448 DegreeTwoThreeSpectrum2725.graph DegreeTwoThreeSpectrum2358.graph
    sourceMap1448 fusedMap1448 sourceMap1448_checked fusedMap1448_checked
    DegreeTwoThreeFiniteComparisons.comparison1448
#print axioms sourceMap1448_checked
#print axioms fusedMap1448_checked
#print axioms certified1448
def sourceMap1448swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1448swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1448swap_checked : acceptsGraphIso
    (source (graph core1448) (root 10) 2 0) DegreeTwoThreeSpectrum2725.graph sourceMap1448swap=true := by decide +kernel
theorem fusedMap1448swap_checked : acceptsGraphIso
    (fused (graph core1448) (root 10) 2 0) DegreeTwoThreeSpectrum2358.graph fusedMap1448swap=true := by decide +kernel
theorem certified1448swap : Certified (graph core1448) (root 10) 2 0 :=
  of_native_maps core1448 DegreeTwoThreeSpectrum2725.graph DegreeTwoThreeSpectrum2358.graph
    sourceMap1448swap fusedMap1448swap sourceMap1448swap_checked fusedMap1448swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1448
#print axioms sourceMap1448swap_checked
#print axioms fusedMap1448swap_checked
#print axioms certified1448swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
