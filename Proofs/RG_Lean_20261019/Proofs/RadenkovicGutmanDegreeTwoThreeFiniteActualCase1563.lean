/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1563 : Family 10 := level10.get ⟨485,by decide⟩
def sourceMap1563 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,9,5,6,7,8,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1563 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1563_checked : acceptsGraphIso
    (source (graph core1563) (root 10) 0 2) DegreeTwoThreeSpectrum2831.graph sourceMap1563=true := by decide +kernel
theorem fusedMap1563_checked : acceptsGraphIso
    (fused (graph core1563) (root 10) 0 2) DegreeTwoThreeSpectrum2971.graph fusedMap1563=true := by decide +kernel
theorem certified1563 : Certified (graph core1563) (root 10) 0 2 :=
  of_native_maps core1563 DegreeTwoThreeSpectrum2831.graph DegreeTwoThreeSpectrum2971.graph
    sourceMap1563 fusedMap1563 sourceMap1563_checked fusedMap1563_checked
    DegreeTwoThreeFiniteComparisons.comparison1563
#print axioms sourceMap1563_checked
#print axioms fusedMap1563_checked
#print axioms certified1563
def sourceMap1563swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,9,5,6,7,2,3,4,8] (sourceLabel 10 2 0 v)
def fusedMap1563swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1563swap_checked : acceptsGraphIso
    (source (graph core1563) (root 10) 2 0) DegreeTwoThreeSpectrum2831.graph sourceMap1563swap=true := by decide +kernel
theorem fusedMap1563swap_checked : acceptsGraphIso
    (fused (graph core1563) (root 10) 2 0) DegreeTwoThreeSpectrum2971.graph fusedMap1563swap=true := by decide +kernel
theorem certified1563swap : Certified (graph core1563) (root 10) 2 0 :=
  of_native_maps core1563 DegreeTwoThreeSpectrum2831.graph DegreeTwoThreeSpectrum2971.graph
    sourceMap1563swap fusedMap1563swap sourceMap1563swap_checked fusedMap1563swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1563
#print axioms sourceMap1563swap_checked
#print axioms fusedMap1563swap_checked
#print axioms certified1563swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
