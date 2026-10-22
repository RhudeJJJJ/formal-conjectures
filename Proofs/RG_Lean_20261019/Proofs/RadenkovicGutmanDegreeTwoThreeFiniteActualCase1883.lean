/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1883 : Family 10 := level10.get ⟨1333,by decide⟩
def sourceMap1883 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1883 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1883_checked : acceptsGraphIso
    (source (graph core1883) (root 10) 0 2) DegreeTwoThreeSpectrum3510.graph sourceMap1883=true := by decide +kernel
theorem fusedMap1883_checked : acceptsGraphIso
    (fused (graph core1883) (root 10) 0 2) DegreeTwoThreeSpectrum3514.graph fusedMap1883=true := by decide +kernel
theorem certified1883 : Certified (graph core1883) (root 10) 0 2 :=
  of_native_maps core1883 DegreeTwoThreeSpectrum3510.graph DegreeTwoThreeSpectrum3514.graph
    sourceMap1883 fusedMap1883 sourceMap1883_checked fusedMap1883_checked
    DegreeTwoThreeFiniteComparisons.comparison1883
#print axioms sourceMap1883_checked
#print axioms fusedMap1883_checked
#print axioms certified1883
def sourceMap1883swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1883swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1883swap_checked : acceptsGraphIso
    (source (graph core1883) (root 10) 2 0) DegreeTwoThreeSpectrum3510.graph sourceMap1883swap=true := by decide +kernel
theorem fusedMap1883swap_checked : acceptsGraphIso
    (fused (graph core1883) (root 10) 2 0) DegreeTwoThreeSpectrum3514.graph fusedMap1883swap=true := by decide +kernel
theorem certified1883swap : Certified (graph core1883) (root 10) 2 0 :=
  of_native_maps core1883 DegreeTwoThreeSpectrum3510.graph DegreeTwoThreeSpectrum3514.graph
    sourceMap1883swap fusedMap1883swap sourceMap1883swap_checked fusedMap1883swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1883
#print axioms sourceMap1883swap_checked
#print axioms fusedMap1883swap_checked
#print axioms certified1883swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
