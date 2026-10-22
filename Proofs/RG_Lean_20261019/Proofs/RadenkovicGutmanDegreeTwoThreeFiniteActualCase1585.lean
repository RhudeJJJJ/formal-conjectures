/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1585 : Family 10 := level10.get ⟨555,by decide⟩
def sourceMap1585 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1585 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1585_checked : acceptsGraphIso
    (source (graph core1585) (root 10) 0 2) DegreeTwoThreeSpectrum3146.graph sourceMap1585=true := by decide +kernel
theorem fusedMap1585_checked : acceptsGraphIso
    (fused (graph core1585) (root 10) 0 2) DegreeTwoThreeSpectrum2497.graph fusedMap1585=true := by decide +kernel
theorem certified1585 : Certified (graph core1585) (root 10) 0 2 :=
  of_native_maps core1585 DegreeTwoThreeSpectrum3146.graph DegreeTwoThreeSpectrum2497.graph
    sourceMap1585 fusedMap1585 sourceMap1585_checked fusedMap1585_checked
    DegreeTwoThreeFiniteComparisons.comparison1585
#print axioms sourceMap1585_checked
#print axioms fusedMap1585_checked
#print axioms certified1585
def sourceMap1585swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1585swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1585swap_checked : acceptsGraphIso
    (source (graph core1585) (root 10) 2 0) DegreeTwoThreeSpectrum3146.graph sourceMap1585swap=true := by decide +kernel
theorem fusedMap1585swap_checked : acceptsGraphIso
    (fused (graph core1585) (root 10) 2 0) DegreeTwoThreeSpectrum2497.graph fusedMap1585swap=true := by decide +kernel
theorem certified1585swap : Certified (graph core1585) (root 10) 2 0 :=
  of_native_maps core1585 DegreeTwoThreeSpectrum3146.graph DegreeTwoThreeSpectrum2497.graph
    sourceMap1585swap fusedMap1585swap sourceMap1585swap_checked fusedMap1585swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1585
#print axioms sourceMap1585swap_checked
#print axioms fusedMap1585swap_checked
#print axioms certified1585swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
