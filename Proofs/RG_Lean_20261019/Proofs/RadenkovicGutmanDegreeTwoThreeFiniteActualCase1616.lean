/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1616 : Family 10 := level10.get ⟨649,by decide⟩
def sourceMap1616 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1616 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1616_checked : acceptsGraphIso
    (source (graph core1616) (root 10) 0 2) DegreeTwoThreeSpectrum3338.graph sourceMap1616=true := by decide +kernel
theorem fusedMap1616_checked : acceptsGraphIso
    (fused (graph core1616) (root 10) 0 2) DegreeTwoThreeSpectrum2597.graph fusedMap1616=true := by decide +kernel
theorem certified1616 : Certified (graph core1616) (root 10) 0 2 :=
  of_native_maps core1616 DegreeTwoThreeSpectrum3338.graph DegreeTwoThreeSpectrum2597.graph
    sourceMap1616 fusedMap1616 sourceMap1616_checked fusedMap1616_checked
    DegreeTwoThreeFiniteComparisons.comparison1616
#print axioms sourceMap1616_checked
#print axioms fusedMap1616_checked
#print axioms certified1616
def sourceMap1616swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1616swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1616swap_checked : acceptsGraphIso
    (source (graph core1616) (root 10) 2 0) DegreeTwoThreeSpectrum3338.graph sourceMap1616swap=true := by decide +kernel
theorem fusedMap1616swap_checked : acceptsGraphIso
    (fused (graph core1616) (root 10) 2 0) DegreeTwoThreeSpectrum2597.graph fusedMap1616swap=true := by decide +kernel
theorem certified1616swap : Certified (graph core1616) (root 10) 2 0 :=
  of_native_maps core1616 DegreeTwoThreeSpectrum3338.graph DegreeTwoThreeSpectrum2597.graph
    sourceMap1616swap fusedMap1616swap sourceMap1616swap_checked fusedMap1616swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1616
#print axioms sourceMap1616swap_checked
#print axioms fusedMap1616swap_checked
#print axioms certified1616swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
