/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1362 : Family 9 := level9.get ⟨506,by decide⟩
def sourceMap1362 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,4,5,6,7,1,2,3] (sourceLabel 9 0 2 v)
def fusedMap1362 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1362_checked : acceptsGraphIso
    (source (graph core1362) (root 9) 0 2) DegreeTwoThreeSpectrum2197.graph sourceMap1362=true := by decide +kernel
theorem fusedMap1362_checked : acceptsGraphIso
    (fused (graph core1362) (root 9) 0 2) DegreeTwoThreeSpectrum2217.graph fusedMap1362=true := by decide +kernel
theorem certified1362 : Certified (graph core1362) (root 9) 0 2 :=
  of_native_maps core1362 DegreeTwoThreeSpectrum2197.graph DegreeTwoThreeSpectrum2217.graph
    sourceMap1362 fusedMap1362 sourceMap1362_checked fusedMap1362_checked
    DegreeTwoThreeFiniteComparisons.comparison1362
#print axioms sourceMap1362_checked
#print axioms fusedMap1362_checked
#print axioms certified1362
def sourceMap1362swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,4,5,6,1,2,3,7] (sourceLabel 9 2 0 v)
def fusedMap1362swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1362swap_checked : acceptsGraphIso
    (source (graph core1362) (root 9) 2 0) DegreeTwoThreeSpectrum2197.graph sourceMap1362swap=true := by decide +kernel
theorem fusedMap1362swap_checked : acceptsGraphIso
    (fused (graph core1362) (root 9) 2 0) DegreeTwoThreeSpectrum2217.graph fusedMap1362swap=true := by decide +kernel
theorem certified1362swap : Certified (graph core1362) (root 9) 2 0 :=
  of_native_maps core1362 DegreeTwoThreeSpectrum2197.graph DegreeTwoThreeSpectrum2217.graph
    sourceMap1362swap fusedMap1362swap sourceMap1362swap_checked fusedMap1362swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1362
#print axioms sourceMap1362swap_checked
#print axioms fusedMap1362swap_checked
#print axioms certified1362swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
