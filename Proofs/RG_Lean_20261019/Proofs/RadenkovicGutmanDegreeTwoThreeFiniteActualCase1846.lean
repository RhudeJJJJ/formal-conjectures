/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1846 : Family 10 := level10.get ⟨1246,by decide⟩
def sourceMap1846 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1846 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1846_checked : acceptsGraphIso
    (source (graph core1846) (root 10) 0 2) DegreeTwoThreeSpectrum3384.graph sourceMap1846=true := by decide +kernel
theorem fusedMap1846_checked : acceptsGraphIso
    (fused (graph core1846) (root 10) 0 2) DegreeTwoThreeSpectrum3385.graph fusedMap1846=true := by decide +kernel
theorem certified1846 : Certified (graph core1846) (root 10) 0 2 :=
  of_native_maps core1846 DegreeTwoThreeSpectrum3384.graph DegreeTwoThreeSpectrum3385.graph
    sourceMap1846 fusedMap1846 sourceMap1846_checked fusedMap1846_checked
    DegreeTwoThreeFiniteComparisons.comparison1846
#print axioms sourceMap1846_checked
#print axioms fusedMap1846_checked
#print axioms certified1846
def sourceMap1846swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1846swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1846swap_checked : acceptsGraphIso
    (source (graph core1846) (root 10) 2 0) DegreeTwoThreeSpectrum3384.graph sourceMap1846swap=true := by decide +kernel
theorem fusedMap1846swap_checked : acceptsGraphIso
    (fused (graph core1846) (root 10) 2 0) DegreeTwoThreeSpectrum3385.graph fusedMap1846swap=true := by decide +kernel
theorem certified1846swap : Certified (graph core1846) (root 10) 2 0 :=
  of_native_maps core1846 DegreeTwoThreeSpectrum3384.graph DegreeTwoThreeSpectrum3385.graph
    sourceMap1846swap fusedMap1846swap sourceMap1846swap_checked fusedMap1846swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1846
#print axioms sourceMap1846swap_checked
#print axioms fusedMap1846swap_checked
#print axioms certified1846swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
