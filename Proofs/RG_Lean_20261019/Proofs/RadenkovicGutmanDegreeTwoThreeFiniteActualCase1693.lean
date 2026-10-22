/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1693 : Family 10 := level10.get ⟨866,by decide⟩
def sourceMap1693 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1693 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1693_checked : acceptsGraphIso
    (source (graph core1693) (root 10) 0 2) DegreeTwoThreeSpectrum3687.graph sourceMap1693=true := by decide +kernel
theorem fusedMap1693_checked : acceptsGraphIso
    (fused (graph core1693) (root 10) 0 2) DegreeTwoThreeSpectrum2858.graph fusedMap1693=true := by decide +kernel
theorem certified1693 : Certified (graph core1693) (root 10) 0 2 :=
  of_native_maps core1693 DegreeTwoThreeSpectrum3687.graph DegreeTwoThreeSpectrum2858.graph
    sourceMap1693 fusedMap1693 sourceMap1693_checked fusedMap1693_checked
    DegreeTwoThreeFiniteComparisons.comparison1693
#print axioms sourceMap1693_checked
#print axioms fusedMap1693_checked
#print axioms certified1693
def sourceMap1693swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1693swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1693swap_checked : acceptsGraphIso
    (source (graph core1693) (root 10) 2 0) DegreeTwoThreeSpectrum3687.graph sourceMap1693swap=true := by decide +kernel
theorem fusedMap1693swap_checked : acceptsGraphIso
    (fused (graph core1693) (root 10) 2 0) DegreeTwoThreeSpectrum2858.graph fusedMap1693swap=true := by decide +kernel
theorem certified1693swap : Certified (graph core1693) (root 10) 2 0 :=
  of_native_maps core1693 DegreeTwoThreeSpectrum3687.graph DegreeTwoThreeSpectrum2858.graph
    sourceMap1693swap fusedMap1693swap sourceMap1693swap_checked fusedMap1693swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1693
#print axioms sourceMap1693swap_checked
#print axioms fusedMap1693swap_checked
#print axioms certified1693swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
