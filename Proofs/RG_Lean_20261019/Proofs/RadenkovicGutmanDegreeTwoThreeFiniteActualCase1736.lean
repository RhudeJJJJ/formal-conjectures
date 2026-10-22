/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1736 : Family 10 := level10.get ⟨967,by decide⟩
def sourceMap1736 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1736 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,5,6,7,8,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1736_checked : acceptsGraphIso
    (source (graph core1736) (root 10) 0 2) DegreeTwoThreeSpectrum3298.graph sourceMap1736=true := by decide +kernel
theorem fusedMap1736_checked : acceptsGraphIso
    (fused (graph core1736) (root 10) 0 2) DegreeTwoThreeSpectrum2947.graph fusedMap1736=true := by decide +kernel
theorem certified1736 : Certified (graph core1736) (root 10) 0 2 :=
  of_native_maps core1736 DegreeTwoThreeSpectrum3298.graph DegreeTwoThreeSpectrum2947.graph
    sourceMap1736 fusedMap1736 sourceMap1736_checked fusedMap1736_checked
    DegreeTwoThreeFiniteComparisons.comparison1736
#print axioms sourceMap1736_checked
#print axioms fusedMap1736_checked
#print axioms certified1736
def sourceMap1736swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1736swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,5,6,7,8,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1736swap_checked : acceptsGraphIso
    (source (graph core1736) (root 10) 2 0) DegreeTwoThreeSpectrum3298.graph sourceMap1736swap=true := by decide +kernel
theorem fusedMap1736swap_checked : acceptsGraphIso
    (fused (graph core1736) (root 10) 2 0) DegreeTwoThreeSpectrum2947.graph fusedMap1736swap=true := by decide +kernel
theorem certified1736swap : Certified (graph core1736) (root 10) 2 0 :=
  of_native_maps core1736 DegreeTwoThreeSpectrum3298.graph DegreeTwoThreeSpectrum2947.graph
    sourceMap1736swap fusedMap1736swap sourceMap1736swap_checked fusedMap1736swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1736
#print axioms sourceMap1736swap_checked
#print axioms fusedMap1736swap_checked
#print axioms certified1736swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
