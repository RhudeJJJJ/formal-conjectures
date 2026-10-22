/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1607 : Family 10 := level10.get ⟨627,by decide⟩
def sourceMap1607 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1607 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1607_checked : acceptsGraphIso
    (source (graph core1607) (root 10) 0 2) DegreeTwoThreeSpectrum3317.graph sourceMap1607=true := by decide +kernel
theorem fusedMap1607_checked : acceptsGraphIso
    (fused (graph core1607) (root 10) 0 2) DegreeTwoThreeSpectrum2571.graph fusedMap1607=true := by decide +kernel
theorem certified1607 : Certified (graph core1607) (root 10) 0 2 :=
  of_native_maps core1607 DegreeTwoThreeSpectrum3317.graph DegreeTwoThreeSpectrum2571.graph
    sourceMap1607 fusedMap1607 sourceMap1607_checked fusedMap1607_checked
    DegreeTwoThreeFiniteComparisons.comparison1607
#print axioms sourceMap1607_checked
#print axioms fusedMap1607_checked
#print axioms certified1607
def sourceMap1607swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1607swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1607swap_checked : acceptsGraphIso
    (source (graph core1607) (root 10) 2 0) DegreeTwoThreeSpectrum3317.graph sourceMap1607swap=true := by decide +kernel
theorem fusedMap1607swap_checked : acceptsGraphIso
    (fused (graph core1607) (root 10) 2 0) DegreeTwoThreeSpectrum2571.graph fusedMap1607swap=true := by decide +kernel
theorem certified1607swap : Certified (graph core1607) (root 10) 2 0 :=
  of_native_maps core1607 DegreeTwoThreeSpectrum3317.graph DegreeTwoThreeSpectrum2571.graph
    sourceMap1607swap fusedMap1607swap sourceMap1607swap_checked fusedMap1607swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1607
#print axioms sourceMap1607swap_checked
#print axioms fusedMap1607swap_checked
#print axioms certified1607swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
