/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1519 : Family 10 := level10.get ⟨358,by decide⟩
def sourceMap1519 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1519 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1519_checked : acceptsGraphIso
    (source (graph core1519) (root 10) 0 2) DegreeTwoThreeSpectrum2800.graph sourceMap1519=true := by decide +kernel
theorem fusedMap1519_checked : acceptsGraphIso
    (fused (graph core1519) (root 10) 0 2) DegreeTwoThreeSpectrum2812.graph fusedMap1519=true := by decide +kernel
theorem certified1519 : Certified (graph core1519) (root 10) 0 2 :=
  of_native_maps core1519 DegreeTwoThreeSpectrum2800.graph DegreeTwoThreeSpectrum2812.graph
    sourceMap1519 fusedMap1519 sourceMap1519_checked fusedMap1519_checked
    DegreeTwoThreeFiniteComparisons.comparison1519
#print axioms sourceMap1519_checked
#print axioms fusedMap1519_checked
#print axioms certified1519
def sourceMap1519swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1519swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1519swap_checked : acceptsGraphIso
    (source (graph core1519) (root 10) 2 0) DegreeTwoThreeSpectrum2800.graph sourceMap1519swap=true := by decide +kernel
theorem fusedMap1519swap_checked : acceptsGraphIso
    (fused (graph core1519) (root 10) 2 0) DegreeTwoThreeSpectrum2812.graph fusedMap1519swap=true := by decide +kernel
theorem certified1519swap : Certified (graph core1519) (root 10) 2 0 :=
  of_native_maps core1519 DegreeTwoThreeSpectrum2800.graph DegreeTwoThreeSpectrum2812.graph
    sourceMap1519swap fusedMap1519swap sourceMap1519swap_checked fusedMap1519swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1519
#print axioms sourceMap1519swap_checked
#print axioms fusedMap1519swap_checked
#print axioms certified1519swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
