/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1583 : Family 10 := level10.get ⟨552,by decide⟩
def sourceMap1583 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1583 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1583_checked : acceptsGraphIso
    (source (graph core1583) (root 10) 0 2) DegreeTwoThreeSpectrum3151.graph sourceMap1583=true := by decide +kernel
theorem fusedMap1583_checked : acceptsGraphIso
    (fused (graph core1583) (root 10) 0 2) DegreeTwoThreeSpectrum2489.graph fusedMap1583=true := by decide +kernel
theorem certified1583 : Certified (graph core1583) (root 10) 0 2 :=
  of_native_maps core1583 DegreeTwoThreeSpectrum3151.graph DegreeTwoThreeSpectrum2489.graph
    sourceMap1583 fusedMap1583 sourceMap1583_checked fusedMap1583_checked
    DegreeTwoThreeFiniteComparisons.comparison1583
#print axioms sourceMap1583_checked
#print axioms fusedMap1583_checked
#print axioms certified1583
def sourceMap1583swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1583swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1583swap_checked : acceptsGraphIso
    (source (graph core1583) (root 10) 2 0) DegreeTwoThreeSpectrum3151.graph sourceMap1583swap=true := by decide +kernel
theorem fusedMap1583swap_checked : acceptsGraphIso
    (fused (graph core1583) (root 10) 2 0) DegreeTwoThreeSpectrum2489.graph fusedMap1583swap=true := by decide +kernel
theorem certified1583swap : Certified (graph core1583) (root 10) 2 0 :=
  of_native_maps core1583 DegreeTwoThreeSpectrum3151.graph DegreeTwoThreeSpectrum2489.graph
    sourceMap1583swap fusedMap1583swap sourceMap1583swap_checked fusedMap1583swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1583
#print axioms sourceMap1583swap_checked
#print axioms fusedMap1583swap_checked
#print axioms certified1583swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
