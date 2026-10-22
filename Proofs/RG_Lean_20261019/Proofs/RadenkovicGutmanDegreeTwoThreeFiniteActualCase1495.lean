/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1495 : Family 10 := level10.get ⟨275,by decide⟩
def sourceMap1495 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1495 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1495_checked : acceptsGraphIso
    (source (graph core1495) (root 10) 0 2) DegreeTwoThreeSpectrum2631.graph sourceMap1495=true := by decide +kernel
theorem fusedMap1495_checked : acceptsGraphIso
    (fused (graph core1495) (root 10) 0 2) DegreeTwoThreeSpectrum2643.graph fusedMap1495=true := by decide +kernel
theorem certified1495 : Certified (graph core1495) (root 10) 0 2 :=
  of_native_maps core1495 DegreeTwoThreeSpectrum2631.graph DegreeTwoThreeSpectrum2643.graph
    sourceMap1495 fusedMap1495 sourceMap1495_checked fusedMap1495_checked
    DegreeTwoThreeFiniteComparisons.comparison1495
#print axioms sourceMap1495_checked
#print axioms fusedMap1495_checked
#print axioms certified1495
def sourceMap1495swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1495swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1495swap_checked : acceptsGraphIso
    (source (graph core1495) (root 10) 2 0) DegreeTwoThreeSpectrum2631.graph sourceMap1495swap=true := by decide +kernel
theorem fusedMap1495swap_checked : acceptsGraphIso
    (fused (graph core1495) (root 10) 2 0) DegreeTwoThreeSpectrum2643.graph fusedMap1495swap=true := by decide +kernel
theorem certified1495swap : Certified (graph core1495) (root 10) 2 0 :=
  of_native_maps core1495 DegreeTwoThreeSpectrum2631.graph DegreeTwoThreeSpectrum2643.graph
    sourceMap1495swap fusedMap1495swap sourceMap1495swap_checked fusedMap1495swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1495
#print axioms sourceMap1495swap_checked
#print axioms fusedMap1495swap_checked
#print axioms certified1495swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
