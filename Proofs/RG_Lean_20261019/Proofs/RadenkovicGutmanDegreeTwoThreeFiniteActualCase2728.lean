/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2728 : Family 10 := level10.get ⟨892,by decide⟩
def sourceMap2728 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2728 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2728_checked : acceptsGraphIso
    (source (graph core2728) (root 10) 0 4) DegreeTwoThreeSpectrum6959.graph sourceMap2728=true := by decide +kernel
theorem fusedMap2728_checked : acceptsGraphIso
    (fused (graph core2728) (root 10) 0 4) DegreeTwoThreeSpectrum5750.graph fusedMap2728=true := by decide +kernel
theorem certified2728 : Certified (graph core2728) (root 10) 0 4 :=
  of_native_maps core2728 DegreeTwoThreeSpectrum6959.graph DegreeTwoThreeSpectrum5750.graph
    sourceMap2728 fusedMap2728 sourceMap2728_checked fusedMap2728_checked
    DegreeTwoThreeFiniteComparisons.comparison2728
#print axioms sourceMap2728_checked
#print axioms fusedMap2728_checked
#print axioms certified2728
def sourceMap2728swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2728swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2728swap_checked : acceptsGraphIso
    (source (graph core2728) (root 10) 4 0) DegreeTwoThreeSpectrum6959.graph sourceMap2728swap=true := by decide +kernel
theorem fusedMap2728swap_checked : acceptsGraphIso
    (fused (graph core2728) (root 10) 4 0) DegreeTwoThreeSpectrum5750.graph fusedMap2728swap=true := by decide +kernel
theorem certified2728swap : Certified (graph core2728) (root 10) 4 0 :=
  of_native_maps core2728 DegreeTwoThreeSpectrum6959.graph DegreeTwoThreeSpectrum5750.graph
    sourceMap2728swap fusedMap2728swap sourceMap2728swap_checked fusedMap2728swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2728
#print axioms sourceMap2728swap_checked
#print axioms fusedMap2728swap_checked
#print axioms certified2728swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
