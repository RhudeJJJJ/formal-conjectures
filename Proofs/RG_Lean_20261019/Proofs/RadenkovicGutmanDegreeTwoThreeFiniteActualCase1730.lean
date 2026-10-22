/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1730 : Family 10 := level10.get ⟨955,by decide⟩
def sourceMap1730 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,8,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1730 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,5,6,7,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1730_checked : acceptsGraphIso
    (source (graph core1730) (root 10) 0 2) DegreeTwoThreeSpectrum3660.graph sourceMap1730=true := by decide +kernel
theorem fusedMap1730_checked : acceptsGraphIso
    (fused (graph core1730) (root 10) 0 2) DegreeTwoThreeSpectrum2968.graph fusedMap1730=true := by decide +kernel
theorem certified1730 : Certified (graph core1730) (root 10) 0 2 :=
  of_native_maps core1730 DegreeTwoThreeSpectrum3660.graph DegreeTwoThreeSpectrum2968.graph
    sourceMap1730 fusedMap1730 sourceMap1730_checked fusedMap1730_checked
    DegreeTwoThreeFiniteComparisons.comparison1730
#print axioms sourceMap1730_checked
#print axioms fusedMap1730_checked
#print axioms certified1730
def sourceMap1730swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,2,3,4,8] (sourceLabel 10 2 0 v)
def fusedMap1730swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,5,6,7,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1730swap_checked : acceptsGraphIso
    (source (graph core1730) (root 10) 2 0) DegreeTwoThreeSpectrum3660.graph sourceMap1730swap=true := by decide +kernel
theorem fusedMap1730swap_checked : acceptsGraphIso
    (fused (graph core1730) (root 10) 2 0) DegreeTwoThreeSpectrum2968.graph fusedMap1730swap=true := by decide +kernel
theorem certified1730swap : Certified (graph core1730) (root 10) 2 0 :=
  of_native_maps core1730 DegreeTwoThreeSpectrum3660.graph DegreeTwoThreeSpectrum2968.graph
    sourceMap1730swap fusedMap1730swap sourceMap1730swap_checked fusedMap1730swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1730
#print axioms sourceMap1730swap_checked
#print axioms fusedMap1730swap_checked
#print axioms certified1730swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
