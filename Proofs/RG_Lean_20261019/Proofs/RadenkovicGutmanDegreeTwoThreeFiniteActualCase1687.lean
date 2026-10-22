/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1687 : Family 10 := level10.get ⟨849,by decide⟩
def sourceMap1687 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1687 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1687_checked : acceptsGraphIso
    (source (graph core1687) (root 10) 0 2) DegreeTwoThreeSpectrum3663.graph sourceMap1687=true := by decide +kernel
theorem fusedMap1687_checked : acceptsGraphIso
    (fused (graph core1687) (root 10) 0 2) DegreeTwoThreeSpectrum2836.graph fusedMap1687=true := by decide +kernel
theorem certified1687 : Certified (graph core1687) (root 10) 0 2 :=
  of_native_maps core1687 DegreeTwoThreeSpectrum3663.graph DegreeTwoThreeSpectrum2836.graph
    sourceMap1687 fusedMap1687 sourceMap1687_checked fusedMap1687_checked
    DegreeTwoThreeFiniteComparisons.comparison1687
#print axioms sourceMap1687_checked
#print axioms fusedMap1687_checked
#print axioms certified1687
def sourceMap1687swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1687swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1687swap_checked : acceptsGraphIso
    (source (graph core1687) (root 10) 2 0) DegreeTwoThreeSpectrum3663.graph sourceMap1687swap=true := by decide +kernel
theorem fusedMap1687swap_checked : acceptsGraphIso
    (fused (graph core1687) (root 10) 2 0) DegreeTwoThreeSpectrum2836.graph fusedMap1687swap=true := by decide +kernel
theorem certified1687swap : Certified (graph core1687) (root 10) 2 0 :=
  of_native_maps core1687 DegreeTwoThreeSpectrum3663.graph DegreeTwoThreeSpectrum2836.graph
    sourceMap1687swap fusedMap1687swap sourceMap1687swap_checked fusedMap1687swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1687
#print axioms sourceMap1687swap_checked
#print axioms fusedMap1687swap_checked
#print axioms certified1687swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
