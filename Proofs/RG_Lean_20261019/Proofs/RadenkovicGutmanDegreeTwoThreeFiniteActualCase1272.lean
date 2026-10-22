/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1272 : Family 9 := level9.get ⟨281,by decide⟩
def sourceMap1272 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,7,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1272 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1272_checked : acceptsGraphIso
    (source (graph core1272) (root 9) 0 2) DegreeTwoThreeSpectrum2212.graph sourceMap1272=true := by decide +kernel
theorem fusedMap1272_checked : acceptsGraphIso
    (fused (graph core1272) (root 9) 0 2) DegreeTwoThreeSpectrum1895.graph fusedMap1272=true := by decide +kernel
theorem certified1272 : Certified (graph core1272) (root 9) 0 2 :=
  of_native_maps core1272 DegreeTwoThreeSpectrum2212.graph DegreeTwoThreeSpectrum1895.graph
    sourceMap1272 fusedMap1272 sourceMap1272_checked fusedMap1272_checked
    DegreeTwoThreeFiniteComparisons.comparison1272
#print axioms sourceMap1272_checked
#print axioms fusedMap1272_checked
#print axioms certified1272
def sourceMap1272swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,2,3,4,7] (sourceLabel 9 2 0 v)
def fusedMap1272swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1272swap_checked : acceptsGraphIso
    (source (graph core1272) (root 9) 2 0) DegreeTwoThreeSpectrum2212.graph sourceMap1272swap=true := by decide +kernel
theorem fusedMap1272swap_checked : acceptsGraphIso
    (fused (graph core1272) (root 9) 2 0) DegreeTwoThreeSpectrum1895.graph fusedMap1272swap=true := by decide +kernel
theorem certified1272swap : Certified (graph core1272) (root 9) 2 0 :=
  of_native_maps core1272 DegreeTwoThreeSpectrum2212.graph DegreeTwoThreeSpectrum1895.graph
    sourceMap1272swap fusedMap1272swap sourceMap1272swap_checked fusedMap1272swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1272
#print axioms sourceMap1272swap_checked
#print axioms fusedMap1272swap_checked
#print axioms certified1272swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
