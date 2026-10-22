/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1602 : Family 10 := level10.get ⟨609,by decide⟩
def sourceMap1602 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,13,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1602 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1602_checked : acceptsGraphIso
    (source (graph core1602) (root 10) 0 2) DegreeTwoThreeSpectrum3271.graph sourceMap1602=true := by decide +kernel
theorem fusedMap1602_checked : acceptsGraphIso
    (fused (graph core1602) (root 10) 0 2) DegreeTwoThreeSpectrum2551.graph fusedMap1602=true := by decide +kernel
theorem certified1602 : Certified (graph core1602) (root 10) 0 2 :=
  of_native_maps core1602 DegreeTwoThreeSpectrum3271.graph DegreeTwoThreeSpectrum2551.graph
    sourceMap1602 fusedMap1602 sourceMap1602_checked fusedMap1602_checked
    DegreeTwoThreeFiniteComparisons.comparison1602
#print axioms sourceMap1602_checked
#print axioms fusedMap1602_checked
#print axioms certified1602
def sourceMap1602swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,8,9,10,13] (sourceLabel 10 2 0 v)
def fusedMap1602swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1602swap_checked : acceptsGraphIso
    (source (graph core1602) (root 10) 2 0) DegreeTwoThreeSpectrum3271.graph sourceMap1602swap=true := by decide +kernel
theorem fusedMap1602swap_checked : acceptsGraphIso
    (fused (graph core1602) (root 10) 2 0) DegreeTwoThreeSpectrum2551.graph fusedMap1602swap=true := by decide +kernel
theorem certified1602swap : Certified (graph core1602) (root 10) 2 0 :=
  of_native_maps core1602 DegreeTwoThreeSpectrum3271.graph DegreeTwoThreeSpectrum2551.graph
    sourceMap1602swap fusedMap1602swap sourceMap1602swap_checked fusedMap1602swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1602
#print axioms sourceMap1602swap_checked
#print axioms fusedMap1602swap_checked
#print axioms certified1602swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
