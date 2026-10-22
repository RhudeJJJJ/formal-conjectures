/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2406 : Family 9 := level9.get ⟨558,by decide⟩
def sourceMap2406 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2406 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2406_checked : acceptsGraphIso
    (source (graph core2406) (root 9) 0 4) DegreeTwoThreeSpectrum4687.graph sourceMap2406=true := by decide +kernel
theorem fusedMap2406_checked : acceptsGraphIso
    (fused (graph core2406) (root 9) 0 4) DegreeTwoThreeSpectrum4194.graph fusedMap2406=true := by decide +kernel
theorem certified2406 : Certified (graph core2406) (root 9) 0 4 :=
  of_native_maps core2406 DegreeTwoThreeSpectrum4687.graph DegreeTwoThreeSpectrum4194.graph
    sourceMap2406 fusedMap2406 sourceMap2406_checked fusedMap2406_checked
    DegreeTwoThreeFiniteComparisons.comparison2406
#print axioms sourceMap2406_checked
#print axioms fusedMap2406_checked
#print axioms certified2406
def sourceMap2406swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2406swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2406swap_checked : acceptsGraphIso
    (source (graph core2406) (root 9) 4 0) DegreeTwoThreeSpectrum4687.graph sourceMap2406swap=true := by decide +kernel
theorem fusedMap2406swap_checked : acceptsGraphIso
    (fused (graph core2406) (root 9) 4 0) DegreeTwoThreeSpectrum4194.graph fusedMap2406swap=true := by decide +kernel
theorem certified2406swap : Certified (graph core2406) (root 9) 4 0 :=
  of_native_maps core2406 DegreeTwoThreeSpectrum4687.graph DegreeTwoThreeSpectrum4194.graph
    sourceMap2406swap fusedMap2406swap sourceMap2406swap_checked fusedMap2406swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2406
#print axioms sourceMap2406swap_checked
#print axioms fusedMap2406swap_checked
#print axioms certified2406swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
