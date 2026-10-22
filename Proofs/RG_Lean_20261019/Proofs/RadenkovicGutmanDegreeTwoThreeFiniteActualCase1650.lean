/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1650 : Family 10 := level10.get ⟨748,by decide⟩
def sourceMap1650 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1650 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1650_checked : acceptsGraphIso
    (source (graph core1650) (root 10) 0 2) DegreeTwoThreeSpectrum3512.graph sourceMap1650=true := by decide +kernel
theorem fusedMap1650_checked : acceptsGraphIso
    (fused (graph core1650) (root 10) 0 2) DegreeTwoThreeSpectrum2710.graph fusedMap1650=true := by decide +kernel
theorem certified1650 : Certified (graph core1650) (root 10) 0 2 :=
  of_native_maps core1650 DegreeTwoThreeSpectrum3512.graph DegreeTwoThreeSpectrum2710.graph
    sourceMap1650 fusedMap1650 sourceMap1650_checked fusedMap1650_checked
    DegreeTwoThreeFiniteComparisons.comparison1650
#print axioms sourceMap1650_checked
#print axioms fusedMap1650_checked
#print axioms certified1650
def sourceMap1650swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1650swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1650swap_checked : acceptsGraphIso
    (source (graph core1650) (root 10) 2 0) DegreeTwoThreeSpectrum3512.graph sourceMap1650swap=true := by decide +kernel
theorem fusedMap1650swap_checked : acceptsGraphIso
    (fused (graph core1650) (root 10) 2 0) DegreeTwoThreeSpectrum2710.graph fusedMap1650swap=true := by decide +kernel
theorem certified1650swap : Certified (graph core1650) (root 10) 2 0 :=
  of_native_maps core1650 DegreeTwoThreeSpectrum3512.graph DegreeTwoThreeSpectrum2710.graph
    sourceMap1650swap fusedMap1650swap sourceMap1650swap_checked fusedMap1650swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1650
#print axioms sourceMap1650swap_checked
#print axioms fusedMap1650swap_checked
#print axioms certified1650swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
