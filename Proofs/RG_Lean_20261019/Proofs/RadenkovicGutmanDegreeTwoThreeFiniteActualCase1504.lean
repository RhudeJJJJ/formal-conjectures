/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1504 : Family 10 := level10.get ⟨302,by decide⟩
def sourceMap1504 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1504 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1504_checked : acceptsGraphIso
    (source (graph core1504) (root 10) 0 2) DegreeTwoThreeSpectrum2682.graph sourceMap1504=true := by decide +kernel
theorem fusedMap1504_checked : acceptsGraphIso
    (fused (graph core1504) (root 10) 0 2) DegreeTwoThreeSpectrum2687.graph fusedMap1504=true := by decide +kernel
theorem certified1504 : Certified (graph core1504) (root 10) 0 2 :=
  of_native_maps core1504 DegreeTwoThreeSpectrum2682.graph DegreeTwoThreeSpectrum2687.graph
    sourceMap1504 fusedMap1504 sourceMap1504_checked fusedMap1504_checked
    DegreeTwoThreeFiniteComparisons.comparison1504
#print axioms sourceMap1504_checked
#print axioms fusedMap1504_checked
#print axioms certified1504
def sourceMap1504swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1504swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1504swap_checked : acceptsGraphIso
    (source (graph core1504) (root 10) 2 0) DegreeTwoThreeSpectrum2682.graph sourceMap1504swap=true := by decide +kernel
theorem fusedMap1504swap_checked : acceptsGraphIso
    (fused (graph core1504) (root 10) 2 0) DegreeTwoThreeSpectrum2687.graph fusedMap1504swap=true := by decide +kernel
theorem certified1504swap : Certified (graph core1504) (root 10) 2 0 :=
  of_native_maps core1504 DegreeTwoThreeSpectrum2682.graph DegreeTwoThreeSpectrum2687.graph
    sourceMap1504swap fusedMap1504swap sourceMap1504swap_checked fusedMap1504swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1504
#print axioms sourceMap1504swap_checked
#print axioms fusedMap1504swap_checked
#print axioms certified1504swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
