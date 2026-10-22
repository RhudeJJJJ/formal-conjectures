/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2264 : Family 9 := level9.get ⟨192,by decide⟩
def sourceMap2264 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2264 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2264_checked : acceptsGraphIso
    (source (graph core2264) (root 9) 0 4) DegreeTwoThreeSpectrum4382.graph sourceMap2264=true := by decide +kernel
theorem fusedMap2264_checked : acceptsGraphIso
    (fused (graph core2264) (root 9) 0 4) DegreeTwoThreeSpectrum3964.graph fusedMap2264=true := by decide +kernel
theorem certified2264 : Certified (graph core2264) (root 9) 0 4 :=
  of_native_maps core2264 DegreeTwoThreeSpectrum4382.graph DegreeTwoThreeSpectrum3964.graph
    sourceMap2264 fusedMap2264 sourceMap2264_checked fusedMap2264_checked
    DegreeTwoThreeFiniteComparisons.comparison2264
#print axioms sourceMap2264_checked
#print axioms fusedMap2264_checked
#print axioms certified2264
def sourceMap2264swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2264swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2264swap_checked : acceptsGraphIso
    (source (graph core2264) (root 9) 4 0) DegreeTwoThreeSpectrum4382.graph sourceMap2264swap=true := by decide +kernel
theorem fusedMap2264swap_checked : acceptsGraphIso
    (fused (graph core2264) (root 9) 4 0) DegreeTwoThreeSpectrum3964.graph fusedMap2264swap=true := by decide +kernel
theorem certified2264swap : Certified (graph core2264) (root 9) 4 0 :=
  of_native_maps core2264 DegreeTwoThreeSpectrum4382.graph DegreeTwoThreeSpectrum3964.graph
    sourceMap2264swap fusedMap2264swap sourceMap2264swap_checked fusedMap2264swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2264
#print axioms sourceMap2264swap_checked
#print axioms fusedMap2264swap_checked
#print axioms certified2264swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
