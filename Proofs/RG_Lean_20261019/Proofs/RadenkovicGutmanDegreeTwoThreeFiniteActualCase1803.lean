/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1803 : Family 10 := level10.get ⟨1142,by decide⟩
def sourceMap1803 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1803 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1803_checked : acceptsGraphIso
    (source (graph core1803) (root 10) 0 2) DegreeTwoThreeSpectrum3229.graph sourceMap1803=true := by decide +kernel
theorem fusedMap1803_checked : acceptsGraphIso
    (fused (graph core1803) (root 10) 0 2) DegreeTwoThreeSpectrum3233.graph fusedMap1803=true := by decide +kernel
theorem certified1803 : Certified (graph core1803) (root 10) 0 2 :=
  of_native_maps core1803 DegreeTwoThreeSpectrum3229.graph DegreeTwoThreeSpectrum3233.graph
    sourceMap1803 fusedMap1803 sourceMap1803_checked fusedMap1803_checked
    DegreeTwoThreeFiniteComparisons.comparison1803
#print axioms sourceMap1803_checked
#print axioms fusedMap1803_checked
#print axioms certified1803
def sourceMap1803swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1803swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1803swap_checked : acceptsGraphIso
    (source (graph core1803) (root 10) 2 0) DegreeTwoThreeSpectrum3229.graph sourceMap1803swap=true := by decide +kernel
theorem fusedMap1803swap_checked : acceptsGraphIso
    (fused (graph core1803) (root 10) 2 0) DegreeTwoThreeSpectrum3233.graph fusedMap1803swap=true := by decide +kernel
theorem certified1803swap : Certified (graph core1803) (root 10) 2 0 :=
  of_native_maps core1803 DegreeTwoThreeSpectrum3229.graph DegreeTwoThreeSpectrum3233.graph
    sourceMap1803swap fusedMap1803swap sourceMap1803swap_checked fusedMap1803swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1803
#print axioms sourceMap1803swap_checked
#print axioms fusedMap1803swap_checked
#print axioms certified1803swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
