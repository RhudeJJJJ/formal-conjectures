/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1498 : Family 10 := level10.get ⟨280,by decide⟩
def sourceMap1498 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1498 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1498_checked : acceptsGraphIso
    (source (graph core1498) (root 10) 0 2) DegreeTwoThreeSpectrum2627.graph sourceMap1498=true := by decide +kernel
theorem fusedMap1498_checked : acceptsGraphIso
    (fused (graph core1498) (root 10) 0 2) DegreeTwoThreeSpectrum2639.graph fusedMap1498=true := by decide +kernel
theorem certified1498 : Certified (graph core1498) (root 10) 0 2 :=
  of_native_maps core1498 DegreeTwoThreeSpectrum2627.graph DegreeTwoThreeSpectrum2639.graph
    sourceMap1498 fusedMap1498 sourceMap1498_checked fusedMap1498_checked
    DegreeTwoThreeFiniteComparisons.comparison1498
#print axioms sourceMap1498_checked
#print axioms fusedMap1498_checked
#print axioms certified1498
def sourceMap1498swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1498swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1498swap_checked : acceptsGraphIso
    (source (graph core1498) (root 10) 2 0) DegreeTwoThreeSpectrum2627.graph sourceMap1498swap=true := by decide +kernel
theorem fusedMap1498swap_checked : acceptsGraphIso
    (fused (graph core1498) (root 10) 2 0) DegreeTwoThreeSpectrum2639.graph fusedMap1498swap=true := by decide +kernel
theorem certified1498swap : Certified (graph core1498) (root 10) 2 0 :=
  of_native_maps core1498 DegreeTwoThreeSpectrum2627.graph DegreeTwoThreeSpectrum2639.graph
    sourceMap1498swap fusedMap1498swap sourceMap1498swap_checked fusedMap1498swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1498
#print axioms sourceMap1498swap_checked
#print axioms fusedMap1498swap_checked
#print axioms certified1498swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
