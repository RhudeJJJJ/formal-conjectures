/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2334 : Family 9 := level9.get ⟨383,by decide⟩
def sourceMap2334 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2334 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2334_checked : acceptsGraphIso
    (source (graph core2334) (root 9) 0 4) DegreeTwoThreeSpectrum4322.graph sourceMap2334=true := by decide +kernel
theorem fusedMap2334_checked : acceptsGraphIso
    (fused (graph core2334) (root 9) 0 4) DegreeTwoThreeSpectrum4323.graph fusedMap2334=true := by decide +kernel
theorem certified2334 : Certified (graph core2334) (root 9) 0 4 :=
  of_native_maps core2334 DegreeTwoThreeSpectrum4322.graph DegreeTwoThreeSpectrum4323.graph
    sourceMap2334 fusedMap2334 sourceMap2334_checked fusedMap2334_checked
    DegreeTwoThreeFiniteComparisons.comparison2334
#print axioms sourceMap2334_checked
#print axioms fusedMap2334_checked
#print axioms certified2334
def sourceMap2334swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2334swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2334swap_checked : acceptsGraphIso
    (source (graph core2334) (root 9) 4 0) DegreeTwoThreeSpectrum4322.graph sourceMap2334swap=true := by decide +kernel
theorem fusedMap2334swap_checked : acceptsGraphIso
    (fused (graph core2334) (root 9) 4 0) DegreeTwoThreeSpectrum4323.graph fusedMap2334swap=true := by decide +kernel
theorem certified2334swap : Certified (graph core2334) (root 9) 4 0 :=
  of_native_maps core2334 DegreeTwoThreeSpectrum4322.graph DegreeTwoThreeSpectrum4323.graph
    sourceMap2334swap fusedMap2334swap sourceMap2334swap_checked fusedMap2334swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2334
#print axioms sourceMap2334swap_checked
#print axioms fusedMap2334swap_checked
#print axioms certified2334swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
