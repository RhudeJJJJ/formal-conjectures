/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1998 : Family 10 := level10.get ⟨1619,by decide⟩
def sourceMap1998 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1998 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1998_checked : acceptsGraphIso
    (source (graph core1998) (root 10) 0 2) DegreeTwoThreeSpectrum3785.graph sourceMap1998=true := by decide +kernel
theorem fusedMap1998_checked : acceptsGraphIso
    (fused (graph core1998) (root 10) 0 2) DegreeTwoThreeSpectrum3160.graph fusedMap1998=true := by decide +kernel
theorem certified1998 : Certified (graph core1998) (root 10) 0 2 :=
  of_native_maps core1998 DegreeTwoThreeSpectrum3785.graph DegreeTwoThreeSpectrum3160.graph
    sourceMap1998 fusedMap1998 sourceMap1998_checked fusedMap1998_checked
    DegreeTwoThreeFiniteComparisons.comparison1998
#print axioms sourceMap1998_checked
#print axioms fusedMap1998_checked
#print axioms certified1998
def sourceMap1998swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1998swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1998swap_checked : acceptsGraphIso
    (source (graph core1998) (root 10) 2 0) DegreeTwoThreeSpectrum3785.graph sourceMap1998swap=true := by decide +kernel
theorem fusedMap1998swap_checked : acceptsGraphIso
    (fused (graph core1998) (root 10) 2 0) DegreeTwoThreeSpectrum3160.graph fusedMap1998swap=true := by decide +kernel
theorem certified1998swap : Certified (graph core1998) (root 10) 2 0 :=
  of_native_maps core1998 DegreeTwoThreeSpectrum3785.graph DegreeTwoThreeSpectrum3160.graph
    sourceMap1998swap fusedMap1998swap sourceMap1998swap_checked fusedMap1998swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1998
#print axioms sourceMap1998swap_checked
#print axioms fusedMap1998swap_checked
#print axioms certified1998swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
