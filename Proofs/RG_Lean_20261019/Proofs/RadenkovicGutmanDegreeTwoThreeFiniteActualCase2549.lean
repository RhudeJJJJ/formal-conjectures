/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2549 : Family 10 := level10.get ⟨380,by decide⟩
def sourceMap2549 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2549 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2549_checked : acceptsGraphIso
    (source (graph core2549) (root 10) 0 4) DegreeTwoThreeSpectrum5701.graph sourceMap2549=true := by decide +kernel
theorem fusedMap2549_checked : acceptsGraphIso
    (fused (graph core2549) (root 10) 0 4) DegreeTwoThreeSpectrum5702.graph fusedMap2549=true := by decide +kernel
theorem certified2549 : Certified (graph core2549) (root 10) 0 4 :=
  of_native_maps core2549 DegreeTwoThreeSpectrum5701.graph DegreeTwoThreeSpectrum5702.graph
    sourceMap2549 fusedMap2549 sourceMap2549_checked fusedMap2549_checked
    DegreeTwoThreeFiniteComparisons.comparison2549
#print axioms sourceMap2549_checked
#print axioms fusedMap2549_checked
#print axioms certified2549
def sourceMap2549swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2549swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2549swap_checked : acceptsGraphIso
    (source (graph core2549) (root 10) 4 0) DegreeTwoThreeSpectrum5701.graph sourceMap2549swap=true := by decide +kernel
theorem fusedMap2549swap_checked : acceptsGraphIso
    (fused (graph core2549) (root 10) 4 0) DegreeTwoThreeSpectrum5702.graph fusedMap2549swap=true := by decide +kernel
theorem certified2549swap : Certified (graph core2549) (root 10) 4 0 :=
  of_native_maps core2549 DegreeTwoThreeSpectrum5701.graph DegreeTwoThreeSpectrum5702.graph
    sourceMap2549swap fusedMap2549swap sourceMap2549swap_checked fusedMap2549swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2549
#print axioms sourceMap2549swap_checked
#print axioms fusedMap2549swap_checked
#print axioms certified2549swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
