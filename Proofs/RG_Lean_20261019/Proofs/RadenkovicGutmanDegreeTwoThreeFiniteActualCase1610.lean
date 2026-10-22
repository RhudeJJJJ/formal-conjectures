/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1610 : Family 10 := level10.get ⟨635,by decide⟩
def sourceMap1610 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1610 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1610_checked : acceptsGraphIso
    (source (graph core1610) (root 10) 0 2) DegreeTwoThreeSpectrum3328.graph sourceMap1610=true := by decide +kernel
theorem fusedMap1610_checked : acceptsGraphIso
    (fused (graph core1610) (root 10) 0 2) DegreeTwoThreeSpectrum2579.graph fusedMap1610=true := by decide +kernel
theorem certified1610 : Certified (graph core1610) (root 10) 0 2 :=
  of_native_maps core1610 DegreeTwoThreeSpectrum3328.graph DegreeTwoThreeSpectrum2579.graph
    sourceMap1610 fusedMap1610 sourceMap1610_checked fusedMap1610_checked
    DegreeTwoThreeFiniteComparisons.comparison1610
#print axioms sourceMap1610_checked
#print axioms fusedMap1610_checked
#print axioms certified1610
def sourceMap1610swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1610swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1610swap_checked : acceptsGraphIso
    (source (graph core1610) (root 10) 2 0) DegreeTwoThreeSpectrum3328.graph sourceMap1610swap=true := by decide +kernel
theorem fusedMap1610swap_checked : acceptsGraphIso
    (fused (graph core1610) (root 10) 2 0) DegreeTwoThreeSpectrum2579.graph fusedMap1610swap=true := by decide +kernel
theorem certified1610swap : Certified (graph core1610) (root 10) 2 0 :=
  of_native_maps core1610 DegreeTwoThreeSpectrum3328.graph DegreeTwoThreeSpectrum2579.graph
    sourceMap1610swap fusedMap1610swap sourceMap1610swap_checked fusedMap1610swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1610
#print axioms sourceMap1610swap_checked
#print axioms fusedMap1610swap_checked
#print axioms certified1610swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
