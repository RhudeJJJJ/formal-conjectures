/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1804 : Family 10 := level10.get ⟨1143,by decide⟩
def sourceMap1804 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1804 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1804_checked : acceptsGraphIso
    (source (graph core1804) (root 10) 0 2) DegreeTwoThreeSpectrum3230.graph sourceMap1804=true := by decide +kernel
theorem fusedMap1804_checked : acceptsGraphIso
    (fused (graph core1804) (root 10) 0 2) DegreeTwoThreeSpectrum3234.graph fusedMap1804=true := by decide +kernel
theorem certified1804 : Certified (graph core1804) (root 10) 0 2 :=
  of_native_maps core1804 DegreeTwoThreeSpectrum3230.graph DegreeTwoThreeSpectrum3234.graph
    sourceMap1804 fusedMap1804 sourceMap1804_checked fusedMap1804_checked
    DegreeTwoThreeFiniteComparisons.comparison1804
#print axioms sourceMap1804_checked
#print axioms fusedMap1804_checked
#print axioms certified1804
def sourceMap1804swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1804swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1804swap_checked : acceptsGraphIso
    (source (graph core1804) (root 10) 2 0) DegreeTwoThreeSpectrum3230.graph sourceMap1804swap=true := by decide +kernel
theorem fusedMap1804swap_checked : acceptsGraphIso
    (fused (graph core1804) (root 10) 2 0) DegreeTwoThreeSpectrum3234.graph fusedMap1804swap=true := by decide +kernel
theorem certified1804swap : Certified (graph core1804) (root 10) 2 0 :=
  of_native_maps core1804 DegreeTwoThreeSpectrum3230.graph DegreeTwoThreeSpectrum3234.graph
    sourceMap1804swap fusedMap1804swap sourceMap1804swap_checked fusedMap1804swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1804
#print axioms sourceMap1804swap_checked
#print axioms fusedMap1804swap_checked
#print axioms certified1804swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
