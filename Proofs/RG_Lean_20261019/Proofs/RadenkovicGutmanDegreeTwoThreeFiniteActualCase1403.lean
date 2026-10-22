/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1403 : Family 9 := level9.get ⟨604,by decide⟩
def sourceMap1403 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1403 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1403_checked : acceptsGraphIso
    (source (graph core1403) (root 9) 0 2) DegreeTwoThreeSpectrum2275.graph sourceMap1403=true := by decide +kernel
theorem fusedMap1403_checked : acceptsGraphIso
    (fused (graph core1403) (root 9) 0 2) DegreeTwoThreeSpectrum2011.graph fusedMap1403=true := by decide +kernel
theorem certified1403 : Certified (graph core1403) (root 9) 0 2 :=
  of_native_maps core1403 DegreeTwoThreeSpectrum2275.graph DegreeTwoThreeSpectrum2011.graph
    sourceMap1403 fusedMap1403 sourceMap1403_checked fusedMap1403_checked
    DegreeTwoThreeFiniteComparisons.comparison1403
#print axioms sourceMap1403_checked
#print axioms fusedMap1403_checked
#print axioms certified1403
def sourceMap1403swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1403swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1403swap_checked : acceptsGraphIso
    (source (graph core1403) (root 9) 2 0) DegreeTwoThreeSpectrum2275.graph sourceMap1403swap=true := by decide +kernel
theorem fusedMap1403swap_checked : acceptsGraphIso
    (fused (graph core1403) (root 9) 2 0) DegreeTwoThreeSpectrum2011.graph fusedMap1403swap=true := by decide +kernel
theorem certified1403swap : Certified (graph core1403) (root 9) 2 0 :=
  of_native_maps core1403 DegreeTwoThreeSpectrum2275.graph DegreeTwoThreeSpectrum2011.graph
    sourceMap1403swap fusedMap1403swap sourceMap1403swap_checked fusedMap1403swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1403
#print axioms sourceMap1403swap_checked
#print axioms fusedMap1403swap_checked
#print axioms certified1403swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
