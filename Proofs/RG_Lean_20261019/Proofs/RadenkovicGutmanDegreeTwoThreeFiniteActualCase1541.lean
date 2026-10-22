/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1541 : Family 10 := level10.get ⟨424,by decide⟩
def sourceMap1541 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1541 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1541_checked : acceptsGraphIso
    (source (graph core1541) (root 10) 0 2) DegreeTwoThreeSpectrum2817.graph sourceMap1541=true := by decide +kernel
theorem fusedMap1541_checked : acceptsGraphIso
    (fused (graph core1541) (root 10) 0 2) DegreeTwoThreeSpectrum2934.graph fusedMap1541=true := by decide +kernel
theorem certified1541 : Certified (graph core1541) (root 10) 0 2 :=
  of_native_maps core1541 DegreeTwoThreeSpectrum2817.graph DegreeTwoThreeSpectrum2934.graph
    sourceMap1541 fusedMap1541 sourceMap1541_checked fusedMap1541_checked
    DegreeTwoThreeFiniteComparisons.comparison1541
#print axioms sourceMap1541_checked
#print axioms fusedMap1541_checked
#print axioms certified1541
def sourceMap1541swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1541swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1541swap_checked : acceptsGraphIso
    (source (graph core1541) (root 10) 2 0) DegreeTwoThreeSpectrum2817.graph sourceMap1541swap=true := by decide +kernel
theorem fusedMap1541swap_checked : acceptsGraphIso
    (fused (graph core1541) (root 10) 2 0) DegreeTwoThreeSpectrum2934.graph fusedMap1541swap=true := by decide +kernel
theorem certified1541swap : Certified (graph core1541) (root 10) 2 0 :=
  of_native_maps core1541 DegreeTwoThreeSpectrum2817.graph DegreeTwoThreeSpectrum2934.graph
    sourceMap1541swap fusedMap1541swap sourceMap1541swap_checked fusedMap1541swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1541
#print axioms sourceMap1541swap_checked
#print axioms fusedMap1541swap_checked
#print axioms certified1541swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
