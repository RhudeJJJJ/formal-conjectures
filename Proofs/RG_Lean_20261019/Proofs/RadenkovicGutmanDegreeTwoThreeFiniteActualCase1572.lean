/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1572 : Family 10 := level10.get ⟨514,by decide⟩
def sourceMap1572 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1572 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1572_checked : acceptsGraphIso
    (source (graph core1572) (root 10) 0 2) DegreeTwoThreeSpectrum3055.graph sourceMap1572=true := by decide +kernel
theorem fusedMap1572_checked : acceptsGraphIso
    (fused (graph core1572) (root 10) 0 2) DegreeTwoThreeSpectrum2453.graph fusedMap1572=true := by decide +kernel
theorem certified1572 : Certified (graph core1572) (root 10) 0 2 :=
  of_native_maps core1572 DegreeTwoThreeSpectrum3055.graph DegreeTwoThreeSpectrum2453.graph
    sourceMap1572 fusedMap1572 sourceMap1572_checked fusedMap1572_checked
    DegreeTwoThreeFiniteComparisons.comparison1572
#print axioms sourceMap1572_checked
#print axioms fusedMap1572_checked
#print axioms certified1572
def sourceMap1572swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1572swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1572swap_checked : acceptsGraphIso
    (source (graph core1572) (root 10) 2 0) DegreeTwoThreeSpectrum3055.graph sourceMap1572swap=true := by decide +kernel
theorem fusedMap1572swap_checked : acceptsGraphIso
    (fused (graph core1572) (root 10) 2 0) DegreeTwoThreeSpectrum2453.graph fusedMap1572swap=true := by decide +kernel
theorem certified1572swap : Certified (graph core1572) (root 10) 2 0 :=
  of_native_maps core1572 DegreeTwoThreeSpectrum3055.graph DegreeTwoThreeSpectrum2453.graph
    sourceMap1572swap fusedMap1572swap sourceMap1572swap_checked fusedMap1572swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1572
#print axioms sourceMap1572swap_checked
#print axioms fusedMap1572swap_checked
#print axioms certified1572swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
