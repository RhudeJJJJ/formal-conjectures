/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2414 : Family 9 := level9.get ⟨577,by decide⟩
def sourceMap2414 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2414 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2414_checked : acceptsGraphIso
    (source (graph core2414) (root 9) 0 4) DegreeTwoThreeSpectrum4708.graph sourceMap2414=true := by decide +kernel
theorem fusedMap2414_checked : acceptsGraphIso
    (fused (graph core2414) (root 9) 0 4) DegreeTwoThreeSpectrum4233.graph fusedMap2414=true := by decide +kernel
theorem certified2414 : Certified (graph core2414) (root 9) 0 4 :=
  of_native_maps core2414 DegreeTwoThreeSpectrum4708.graph DegreeTwoThreeSpectrum4233.graph
    sourceMap2414 fusedMap2414 sourceMap2414_checked fusedMap2414_checked
    DegreeTwoThreeFiniteComparisons.comparison2414
#print axioms sourceMap2414_checked
#print axioms fusedMap2414_checked
#print axioms certified2414
def sourceMap2414swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2414swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2414swap_checked : acceptsGraphIso
    (source (graph core2414) (root 9) 4 0) DegreeTwoThreeSpectrum4708.graph sourceMap2414swap=true := by decide +kernel
theorem fusedMap2414swap_checked : acceptsGraphIso
    (fused (graph core2414) (root 9) 4 0) DegreeTwoThreeSpectrum4233.graph fusedMap2414swap=true := by decide +kernel
theorem certified2414swap : Certified (graph core2414) (root 9) 4 0 :=
  of_native_maps core2414 DegreeTwoThreeSpectrum4708.graph DegreeTwoThreeSpectrum4233.graph
    sourceMap2414swap fusedMap2414swap sourceMap2414swap_checked fusedMap2414swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2414
#print axioms sourceMap2414swap_checked
#print axioms fusedMap2414swap_checked
#print axioms certified2414swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
