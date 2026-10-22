/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1571 : Family 10 := level10.get ⟨513,by decide⟩
def sourceMap1571 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1571 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1571_checked : acceptsGraphIso
    (source (graph core1571) (root 10) 0 2) DegreeTwoThreeSpectrum3056.graph sourceMap1571=true := by decide +kernel
theorem fusedMap1571_checked : acceptsGraphIso
    (fused (graph core1571) (root 10) 0 2) DegreeTwoThreeSpectrum2450.graph fusedMap1571=true := by decide +kernel
theorem certified1571 : Certified (graph core1571) (root 10) 0 2 :=
  of_native_maps core1571 DegreeTwoThreeSpectrum3056.graph DegreeTwoThreeSpectrum2450.graph
    sourceMap1571 fusedMap1571 sourceMap1571_checked fusedMap1571_checked
    DegreeTwoThreeFiniteComparisons.comparison1571
#print axioms sourceMap1571_checked
#print axioms fusedMap1571_checked
#print axioms certified1571
def sourceMap1571swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1571swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1571swap_checked : acceptsGraphIso
    (source (graph core1571) (root 10) 2 0) DegreeTwoThreeSpectrum3056.graph sourceMap1571swap=true := by decide +kernel
theorem fusedMap1571swap_checked : acceptsGraphIso
    (fused (graph core1571) (root 10) 2 0) DegreeTwoThreeSpectrum2450.graph fusedMap1571swap=true := by decide +kernel
theorem certified1571swap : Certified (graph core1571) (root 10) 2 0 :=
  of_native_maps core1571 DegreeTwoThreeSpectrum3056.graph DegreeTwoThreeSpectrum2450.graph
    sourceMap1571swap fusedMap1571swap sourceMap1571swap_checked fusedMap1571swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1571
#print axioms sourceMap1571swap_checked
#print axioms fusedMap1571swap_checked
#print axioms certified1571swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
