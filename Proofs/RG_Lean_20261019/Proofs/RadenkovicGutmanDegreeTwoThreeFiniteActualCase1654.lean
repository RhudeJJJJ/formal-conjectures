/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1654 : Family 10 := level10.get ⟨757,by decide⟩
def sourceMap1654 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,13,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1654 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1654_checked : acceptsGraphIso
    (source (graph core1654) (root 10) 0 2) DegreeTwoThreeSpectrum3520.graph sourceMap1654=true := by decide +kernel
theorem fusedMap1654_checked : acceptsGraphIso
    (fused (graph core1654) (root 10) 0 2) DegreeTwoThreeSpectrum2721.graph fusedMap1654=true := by decide +kernel
theorem certified1654 : Certified (graph core1654) (root 10) 0 2 :=
  of_native_maps core1654 DegreeTwoThreeSpectrum3520.graph DegreeTwoThreeSpectrum2721.graph
    sourceMap1654 fusedMap1654 sourceMap1654_checked fusedMap1654_checked
    DegreeTwoThreeFiniteComparisons.comparison1654
#print axioms sourceMap1654_checked
#print axioms fusedMap1654_checked
#print axioms certified1654
def sourceMap1654swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,8,9,10,13] (sourceLabel 10 2 0 v)
def fusedMap1654swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1654swap_checked : acceptsGraphIso
    (source (graph core1654) (root 10) 2 0) DegreeTwoThreeSpectrum3520.graph sourceMap1654swap=true := by decide +kernel
theorem fusedMap1654swap_checked : acceptsGraphIso
    (fused (graph core1654) (root 10) 2 0) DegreeTwoThreeSpectrum2721.graph fusedMap1654swap=true := by decide +kernel
theorem certified1654swap : Certified (graph core1654) (root 10) 2 0 :=
  of_native_maps core1654 DegreeTwoThreeSpectrum3520.graph DegreeTwoThreeSpectrum2721.graph
    sourceMap1654swap fusedMap1654swap sourceMap1654swap_checked fusedMap1654swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1654
#print axioms sourceMap1654swap_checked
#print axioms fusedMap1654swap_checked
#print axioms certified1654swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
