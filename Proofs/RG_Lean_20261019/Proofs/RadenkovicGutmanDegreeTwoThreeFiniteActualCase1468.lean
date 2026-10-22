/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1468 : Family 10 := level10.get ⟨175,by decide⟩
def sourceMap1468 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,6,7,8,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1468 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1468_checked : acceptsGraphIso
    (source (graph core1468) (root 10) 0 2) DegreeTwoThreeSpectrum2856.graph sourceMap1468=true := by decide +kernel
theorem fusedMap1468_checked : acceptsGraphIso
    (fused (graph core1468) (root 10) 0 2) DegreeTwoThreeSpectrum2413.graph fusedMap1468=true := by decide +kernel
theorem certified1468 : Certified (graph core1468) (root 10) 0 2 :=
  of_native_maps core1468 DegreeTwoThreeSpectrum2856.graph DegreeTwoThreeSpectrum2413.graph
    sourceMap1468 fusedMap1468 sourceMap1468_checked fusedMap1468_checked
    DegreeTwoThreeFiniteComparisons.comparison1468
#print axioms sourceMap1468_checked
#print axioms fusedMap1468_checked
#print axioms certified1468
def sourceMap1468swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,6,7,3,4,5,8] (sourceLabel 10 2 0 v)
def fusedMap1468swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1468swap_checked : acceptsGraphIso
    (source (graph core1468) (root 10) 2 0) DegreeTwoThreeSpectrum2856.graph sourceMap1468swap=true := by decide +kernel
theorem fusedMap1468swap_checked : acceptsGraphIso
    (fused (graph core1468) (root 10) 2 0) DegreeTwoThreeSpectrum2413.graph fusedMap1468swap=true := by decide +kernel
theorem certified1468swap : Certified (graph core1468) (root 10) 2 0 :=
  of_native_maps core1468 DegreeTwoThreeSpectrum2856.graph DegreeTwoThreeSpectrum2413.graph
    sourceMap1468swap fusedMap1468swap sourceMap1468swap_checked fusedMap1468swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1468
#print axioms sourceMap1468swap_checked
#print axioms fusedMap1468swap_checked
#print axioms certified1468swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
