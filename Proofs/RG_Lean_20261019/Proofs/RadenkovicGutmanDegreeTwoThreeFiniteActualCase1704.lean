/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1704 : Family 10 := level10.get ⟨891,by decide⟩
def sourceMap1704 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1704 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1704_checked : acceptsGraphIso
    (source (graph core1704) (root 10) 0 2) DegreeTwoThreeSpectrum3626.graph sourceMap1704=true := by decide +kernel
theorem fusedMap1704_checked : acceptsGraphIso
    (fused (graph core1704) (root 10) 0 2) DegreeTwoThreeSpectrum2901.graph fusedMap1704=true := by decide +kernel
theorem certified1704 : Certified (graph core1704) (root 10) 0 2 :=
  of_native_maps core1704 DegreeTwoThreeSpectrum3626.graph DegreeTwoThreeSpectrum2901.graph
    sourceMap1704 fusedMap1704 sourceMap1704_checked fusedMap1704_checked
    DegreeTwoThreeFiniteComparisons.comparison1704
#print axioms sourceMap1704_checked
#print axioms fusedMap1704_checked
#print axioms certified1704
def sourceMap1704swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1704swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1704swap_checked : acceptsGraphIso
    (source (graph core1704) (root 10) 2 0) DegreeTwoThreeSpectrum3626.graph sourceMap1704swap=true := by decide +kernel
theorem fusedMap1704swap_checked : acceptsGraphIso
    (fused (graph core1704) (root 10) 2 0) DegreeTwoThreeSpectrum2901.graph fusedMap1704swap=true := by decide +kernel
theorem certified1704swap : Certified (graph core1704) (root 10) 2 0 :=
  of_native_maps core1704 DegreeTwoThreeSpectrum3626.graph DegreeTwoThreeSpectrum2901.graph
    sourceMap1704swap fusedMap1704swap sourceMap1704swap_checked fusedMap1704swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1704
#print axioms sourceMap1704swap_checked
#print axioms fusedMap1704swap_checked
#print axioms certified1704swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
