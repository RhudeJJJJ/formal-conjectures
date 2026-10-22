/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1713 : Family 10 := level10.get ⟨913,by decide⟩
def sourceMap1713 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,8,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1713 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1713_checked : acceptsGraphIso
    (source (graph core1713) (root 10) 0 2) DegreeTwoThreeSpectrum3659.graph sourceMap1713=true := by decide +kernel
theorem fusedMap1713_checked : acceptsGraphIso
    (fused (graph core1713) (root 10) 0 2) DegreeTwoThreeSpectrum2926.graph fusedMap1713=true := by decide +kernel
theorem certified1713 : Certified (graph core1713) (root 10) 0 2 :=
  of_native_maps core1713 DegreeTwoThreeSpectrum3659.graph DegreeTwoThreeSpectrum2926.graph
    sourceMap1713 fusedMap1713 sourceMap1713_checked fusedMap1713_checked
    DegreeTwoThreeFiniteComparisons.comparison1713
#print axioms sourceMap1713_checked
#print axioms fusedMap1713_checked
#print axioms certified1713
def sourceMap1713swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,2,3,4,8] (sourceLabel 10 2 0 v)
def fusedMap1713swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1713swap_checked : acceptsGraphIso
    (source (graph core1713) (root 10) 2 0) DegreeTwoThreeSpectrum3659.graph sourceMap1713swap=true := by decide +kernel
theorem fusedMap1713swap_checked : acceptsGraphIso
    (fused (graph core1713) (root 10) 2 0) DegreeTwoThreeSpectrum2926.graph fusedMap1713swap=true := by decide +kernel
theorem certified1713swap : Certified (graph core1713) (root 10) 2 0 :=
  of_native_maps core1713 DegreeTwoThreeSpectrum3659.graph DegreeTwoThreeSpectrum2926.graph
    sourceMap1713swap fusedMap1713swap sourceMap1713swap_checked fusedMap1713swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1713
#print axioms sourceMap1713swap_checked
#print axioms fusedMap1713swap_checked
#print axioms certified1713swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
