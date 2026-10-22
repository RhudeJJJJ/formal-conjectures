/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1590 : Family 10 := level10.get ⟨574,by decide⟩
def sourceMap1590 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1590 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1590_checked : acceptsGraphIso
    (source (graph core1590) (root 10) 0 2) DegreeTwoThreeSpectrum3202.graph sourceMap1590=true := by decide +kernel
theorem fusedMap1590_checked : acceptsGraphIso
    (fused (graph core1590) (root 10) 0 2) DegreeTwoThreeSpectrum2515.graph fusedMap1590=true := by decide +kernel
theorem certified1590 : Certified (graph core1590) (root 10) 0 2 :=
  of_native_maps core1590 DegreeTwoThreeSpectrum3202.graph DegreeTwoThreeSpectrum2515.graph
    sourceMap1590 fusedMap1590 sourceMap1590_checked fusedMap1590_checked
    DegreeTwoThreeFiniteComparisons.comparison1590
#print axioms sourceMap1590_checked
#print axioms fusedMap1590_checked
#print axioms certified1590
def sourceMap1590swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1590swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1590swap_checked : acceptsGraphIso
    (source (graph core1590) (root 10) 2 0) DegreeTwoThreeSpectrum3202.graph sourceMap1590swap=true := by decide +kernel
theorem fusedMap1590swap_checked : acceptsGraphIso
    (fused (graph core1590) (root 10) 2 0) DegreeTwoThreeSpectrum2515.graph fusedMap1590swap=true := by decide +kernel
theorem certified1590swap : Certified (graph core1590) (root 10) 2 0 :=
  of_native_maps core1590 DegreeTwoThreeSpectrum3202.graph DegreeTwoThreeSpectrum2515.graph
    sourceMap1590swap fusedMap1590swap sourceMap1590swap_checked fusedMap1590swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1590
#print axioms sourceMap1590swap_checked
#print axioms fusedMap1590swap_checked
#print axioms certified1590swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
