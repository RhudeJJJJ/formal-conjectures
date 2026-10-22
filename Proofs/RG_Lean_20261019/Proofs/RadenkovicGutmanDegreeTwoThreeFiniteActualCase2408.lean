/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2408 : Family 9 := level9.get ⟨566,by decide⟩
def sourceMap2408 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2408 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2408_checked : acceptsGraphIso
    (source (graph core2408) (root 9) 0 4) DegreeTwoThreeSpectrum4696.graph sourceMap2408=true := by decide +kernel
theorem fusedMap2408_checked : acceptsGraphIso
    (fused (graph core2408) (root 9) 0 4) DegreeTwoThreeSpectrum4209.graph fusedMap2408=true := by decide +kernel
theorem certified2408 : Certified (graph core2408) (root 9) 0 4 :=
  of_native_maps core2408 DegreeTwoThreeSpectrum4696.graph DegreeTwoThreeSpectrum4209.graph
    sourceMap2408 fusedMap2408 sourceMap2408_checked fusedMap2408_checked
    DegreeTwoThreeFiniteComparisons.comparison2408
#print axioms sourceMap2408_checked
#print axioms fusedMap2408_checked
#print axioms certified2408
def sourceMap2408swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2408swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2408swap_checked : acceptsGraphIso
    (source (graph core2408) (root 9) 4 0) DegreeTwoThreeSpectrum4696.graph sourceMap2408swap=true := by decide +kernel
theorem fusedMap2408swap_checked : acceptsGraphIso
    (fused (graph core2408) (root 9) 4 0) DegreeTwoThreeSpectrum4209.graph fusedMap2408swap=true := by decide +kernel
theorem certified2408swap : Certified (graph core2408) (root 9) 4 0 :=
  of_native_maps core2408 DegreeTwoThreeSpectrum4696.graph DegreeTwoThreeSpectrum4209.graph
    sourceMap2408swap fusedMap2408swap sourceMap2408swap_checked fusedMap2408swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2408
#print axioms sourceMap2408swap_checked
#print axioms fusedMap2408swap_checked
#print axioms certified2408swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
