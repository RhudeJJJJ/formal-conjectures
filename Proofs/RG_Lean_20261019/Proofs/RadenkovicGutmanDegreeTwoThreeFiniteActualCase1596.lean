/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1596 : Family 10 := level10.get ⟨594,by decide⟩
def sourceMap1596 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1596 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1596_checked : acceptsGraphIso
    (source (graph core1596) (root 10) 0 2) DegreeTwoThreeSpectrum3252.graph sourceMap1596=true := by decide +kernel
theorem fusedMap1596_checked : acceptsGraphIso
    (fused (graph core1596) (root 10) 0 2) DegreeTwoThreeSpectrum2535.graph fusedMap1596=true := by decide +kernel
theorem certified1596 : Certified (graph core1596) (root 10) 0 2 :=
  of_native_maps core1596 DegreeTwoThreeSpectrum3252.graph DegreeTwoThreeSpectrum2535.graph
    sourceMap1596 fusedMap1596 sourceMap1596_checked fusedMap1596_checked
    DegreeTwoThreeFiniteComparisons.comparison1596
#print axioms sourceMap1596_checked
#print axioms fusedMap1596_checked
#print axioms certified1596
def sourceMap1596swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1596swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1596swap_checked : acceptsGraphIso
    (source (graph core1596) (root 10) 2 0) DegreeTwoThreeSpectrum3252.graph sourceMap1596swap=true := by decide +kernel
theorem fusedMap1596swap_checked : acceptsGraphIso
    (fused (graph core1596) (root 10) 2 0) DegreeTwoThreeSpectrum2535.graph fusedMap1596swap=true := by decide +kernel
theorem certified1596swap : Certified (graph core1596) (root 10) 2 0 :=
  of_native_maps core1596 DegreeTwoThreeSpectrum3252.graph DegreeTwoThreeSpectrum2535.graph
    sourceMap1596swap fusedMap1596swap sourceMap1596swap_checked fusedMap1596swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1596
#print axioms sourceMap1596swap_checked
#print axioms fusedMap1596swap_checked
#print axioms certified1596swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
