/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1349 : Family 9 := level9.get ⟨477,by decide⟩
def sourceMap1349 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1349 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1349_checked : acceptsGraphIso
    (source (graph core1349) (root 9) 0 2) DegreeTwoThreeSpectrum2177.graph sourceMap1349=true := by decide +kernel
theorem fusedMap1349_checked : acceptsGraphIso
    (fused (graph core1349) (root 9) 0 2) DegreeTwoThreeSpectrum2174.graph fusedMap1349=true := by decide +kernel
theorem certified1349 : Certified (graph core1349) (root 9) 0 2 :=
  of_native_maps core1349 DegreeTwoThreeSpectrum2177.graph DegreeTwoThreeSpectrum2174.graph
    sourceMap1349 fusedMap1349 sourceMap1349_checked fusedMap1349_checked
    DegreeTwoThreeFiniteComparisons.comparison1349
#print axioms sourceMap1349_checked
#print axioms fusedMap1349_checked
#print axioms certified1349
def sourceMap1349swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1349swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1349swap_checked : acceptsGraphIso
    (source (graph core1349) (root 9) 2 0) DegreeTwoThreeSpectrum2177.graph sourceMap1349swap=true := by decide +kernel
theorem fusedMap1349swap_checked : acceptsGraphIso
    (fused (graph core1349) (root 9) 2 0) DegreeTwoThreeSpectrum2174.graph fusedMap1349swap=true := by decide +kernel
theorem certified1349swap : Certified (graph core1349) (root 9) 2 0 :=
  of_native_maps core1349 DegreeTwoThreeSpectrum2177.graph DegreeTwoThreeSpectrum2174.graph
    sourceMap1349swap fusedMap1349swap sourceMap1349swap_checked fusedMap1349swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1349
#print axioms sourceMap1349swap_checked
#print axioms fusedMap1349swap_checked
#print axioms certified1349swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
