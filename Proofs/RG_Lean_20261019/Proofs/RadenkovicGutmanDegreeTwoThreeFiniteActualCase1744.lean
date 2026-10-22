/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1744 : Family 10 := level10.get ⟨981,by decide⟩
def sourceMap1744 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1744 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1744_checked : acceptsGraphIso
    (source (graph core1744) (root 10) 0 2) DegreeTwoThreeSpectrum3241.graph sourceMap1744=true := by decide +kernel
theorem fusedMap1744_checked : acceptsGraphIso
    (fused (graph core1744) (root 10) 0 2) DegreeTwoThreeSpectrum2945.graph fusedMap1744=true := by decide +kernel
theorem certified1744 : Certified (graph core1744) (root 10) 0 2 :=
  of_native_maps core1744 DegreeTwoThreeSpectrum3241.graph DegreeTwoThreeSpectrum2945.graph
    sourceMap1744 fusedMap1744 sourceMap1744_checked fusedMap1744_checked
    DegreeTwoThreeFiniteComparisons.comparison1744
#print axioms sourceMap1744_checked
#print axioms fusedMap1744_checked
#print axioms certified1744
def sourceMap1744swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1744swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1744swap_checked : acceptsGraphIso
    (source (graph core1744) (root 10) 2 0) DegreeTwoThreeSpectrum3241.graph sourceMap1744swap=true := by decide +kernel
theorem fusedMap1744swap_checked : acceptsGraphIso
    (fused (graph core1744) (root 10) 2 0) DegreeTwoThreeSpectrum2945.graph fusedMap1744swap=true := by decide +kernel
theorem certified1744swap : Certified (graph core1744) (root 10) 2 0 :=
  of_native_maps core1744 DegreeTwoThreeSpectrum3241.graph DegreeTwoThreeSpectrum2945.graph
    sourceMap1744swap fusedMap1744swap sourceMap1744swap_checked fusedMap1744swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1744
#print axioms sourceMap1744swap_checked
#print axioms fusedMap1744swap_checked
#print axioms certified1744swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
