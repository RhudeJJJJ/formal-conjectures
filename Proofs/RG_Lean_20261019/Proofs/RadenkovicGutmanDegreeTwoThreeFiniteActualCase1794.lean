/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1794 : Family 10 := level10.get ⟨1120,by decide⟩
def sourceMap1794 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1794 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1794_checked : acceptsGraphIso
    (source (graph core1794) (root 10) 0 2) DegreeTwoThreeSpectrum3196.graph sourceMap1794=true := by decide +kernel
theorem fusedMap1794_checked : acceptsGraphIso
    (fused (graph core1794) (root 10) 0 2) DegreeTwoThreeSpectrum3198.graph fusedMap1794=true := by decide +kernel
theorem certified1794 : Certified (graph core1794) (root 10) 0 2 :=
  of_native_maps core1794 DegreeTwoThreeSpectrum3196.graph DegreeTwoThreeSpectrum3198.graph
    sourceMap1794 fusedMap1794 sourceMap1794_checked fusedMap1794_checked
    DegreeTwoThreeFiniteComparisons.comparison1794
#print axioms sourceMap1794_checked
#print axioms fusedMap1794_checked
#print axioms certified1794
def sourceMap1794swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1794swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1794swap_checked : acceptsGraphIso
    (source (graph core1794) (root 10) 2 0) DegreeTwoThreeSpectrum3196.graph sourceMap1794swap=true := by decide +kernel
theorem fusedMap1794swap_checked : acceptsGraphIso
    (fused (graph core1794) (root 10) 2 0) DegreeTwoThreeSpectrum3198.graph fusedMap1794swap=true := by decide +kernel
theorem certified1794swap : Certified (graph core1794) (root 10) 2 0 :=
  of_native_maps core1794 DegreeTwoThreeSpectrum3196.graph DegreeTwoThreeSpectrum3198.graph
    sourceMap1794swap fusedMap1794swap sourceMap1794swap_checked fusedMap1794swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1794
#print axioms sourceMap1794swap_checked
#print axioms fusedMap1794swap_checked
#print axioms certified1794swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
