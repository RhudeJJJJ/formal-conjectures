/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1553 : Family 10 := level10.get ⟨461,by decide⟩
def sourceMap1553 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1553 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1553_checked : acceptsGraphIso
    (source (graph core1553) (root 10) 0 2) DegreeTwoThreeSpectrum2847.graph sourceMap1553=true := by decide +kernel
theorem fusedMap1553_checked : acceptsGraphIso
    (fused (graph core1553) (root 10) 0 2) DegreeTwoThreeSpectrum2980.graph fusedMap1553=true := by decide +kernel
theorem certified1553 : Certified (graph core1553) (root 10) 0 2 :=
  of_native_maps core1553 DegreeTwoThreeSpectrum2847.graph DegreeTwoThreeSpectrum2980.graph
    sourceMap1553 fusedMap1553 sourceMap1553_checked fusedMap1553_checked
    DegreeTwoThreeFiniteComparisons.comparison1553
#print axioms sourceMap1553_checked
#print axioms fusedMap1553_checked
#print axioms certified1553
def sourceMap1553swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1553swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1553swap_checked : acceptsGraphIso
    (source (graph core1553) (root 10) 2 0) DegreeTwoThreeSpectrum2847.graph sourceMap1553swap=true := by decide +kernel
theorem fusedMap1553swap_checked : acceptsGraphIso
    (fused (graph core1553) (root 10) 2 0) DegreeTwoThreeSpectrum2980.graph fusedMap1553swap=true := by decide +kernel
theorem certified1553swap : Certified (graph core1553) (root 10) 2 0 :=
  of_native_maps core1553 DegreeTwoThreeSpectrum2847.graph DegreeTwoThreeSpectrum2980.graph
    sourceMap1553swap fusedMap1553swap sourceMap1553swap_checked fusedMap1553swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1553
#print axioms sourceMap1553swap_checked
#print axioms fusedMap1553swap_checked
#print axioms certified1553swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
