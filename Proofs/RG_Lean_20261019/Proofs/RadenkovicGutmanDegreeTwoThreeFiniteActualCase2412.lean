/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2412 : Family 9 := level9.get ⟨573,by decide⟩
def sourceMap2412 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2412 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2412_checked : acceptsGraphIso
    (source (graph core2412) (root 9) 0 4) DegreeTwoThreeSpectrum4702.graph sourceMap2412=true := by decide +kernel
theorem fusedMap2412_checked : acceptsGraphIso
    (fused (graph core2412) (root 9) 0 4) DegreeTwoThreeSpectrum4222.graph fusedMap2412=true := by decide +kernel
theorem certified2412 : Certified (graph core2412) (root 9) 0 4 :=
  of_native_maps core2412 DegreeTwoThreeSpectrum4702.graph DegreeTwoThreeSpectrum4222.graph
    sourceMap2412 fusedMap2412 sourceMap2412_checked fusedMap2412_checked
    DegreeTwoThreeFiniteComparisons.comparison2412
#print axioms sourceMap2412_checked
#print axioms fusedMap2412_checked
#print axioms certified2412
def sourceMap2412swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2412swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2412swap_checked : acceptsGraphIso
    (source (graph core2412) (root 9) 4 0) DegreeTwoThreeSpectrum4702.graph sourceMap2412swap=true := by decide +kernel
theorem fusedMap2412swap_checked : acceptsGraphIso
    (fused (graph core2412) (root 9) 4 0) DegreeTwoThreeSpectrum4222.graph fusedMap2412swap=true := by decide +kernel
theorem certified2412swap : Certified (graph core2412) (root 9) 4 0 :=
  of_native_maps core2412 DegreeTwoThreeSpectrum4702.graph DegreeTwoThreeSpectrum4222.graph
    sourceMap2412swap fusedMap2412swap sourceMap2412swap_checked fusedMap2412swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2412
#print axioms sourceMap2412swap_checked
#print axioms fusedMap2412swap_checked
#print axioms certified2412swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
