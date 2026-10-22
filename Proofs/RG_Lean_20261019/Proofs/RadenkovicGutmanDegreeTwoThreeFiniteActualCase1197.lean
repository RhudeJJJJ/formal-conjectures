/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1197 : Family 9 := level9.get ⟨37,by decide⟩
def sourceMap1197 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,6,7,3,4,5] (sourceLabel 9 0 2 v)
def fusedMap1197 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1197_checked : acceptsGraphIso
    (source (graph core1197) (root 9) 0 2) DegreeTwoThreeSpectrum1889.graph sourceMap1197=true := by decide +kernel
theorem fusedMap1197_checked : acceptsGraphIso
    (fused (graph core1197) (root 9) 0 2) DegreeTwoThreeSpectrum1733.graph fusedMap1197=true := by decide +kernel
theorem certified1197 : Certified (graph core1197) (root 9) 0 2 :=
  of_native_maps core1197 DegreeTwoThreeSpectrum1889.graph DegreeTwoThreeSpectrum1733.graph
    sourceMap1197 fusedMap1197 sourceMap1197_checked fusedMap1197_checked
    DegreeTwoThreeFiniteComparisons.comparison1197
#print axioms sourceMap1197_checked
#print axioms fusedMap1197_checked
#print axioms certified1197
def sourceMap1197swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,6,3,4,5,7] (sourceLabel 9 2 0 v)
def fusedMap1197swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1197swap_checked : acceptsGraphIso
    (source (graph core1197) (root 9) 2 0) DegreeTwoThreeSpectrum1889.graph sourceMap1197swap=true := by decide +kernel
theorem fusedMap1197swap_checked : acceptsGraphIso
    (fused (graph core1197) (root 9) 2 0) DegreeTwoThreeSpectrum1733.graph fusedMap1197swap=true := by decide +kernel
theorem certified1197swap : Certified (graph core1197) (root 9) 2 0 :=
  of_native_maps core1197 DegreeTwoThreeSpectrum1889.graph DegreeTwoThreeSpectrum1733.graph
    sourceMap1197swap fusedMap1197swap sourceMap1197swap_checked fusedMap1197swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1197
#print axioms sourceMap1197swap_checked
#print axioms fusedMap1197swap_checked
#print axioms certified1197swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
