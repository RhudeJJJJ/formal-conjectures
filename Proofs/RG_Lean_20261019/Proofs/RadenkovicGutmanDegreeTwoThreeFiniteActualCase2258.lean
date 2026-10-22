/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2258 : Family 9 := level9.get ⟨172,by decide⟩
def sourceMap2258 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2258 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2258_checked : acceptsGraphIso
    (source (graph core2258) (root 9) 0 4) DegreeTwoThreeSpectrum4328.graph sourceMap2258=true := by decide +kernel
theorem fusedMap2258_checked : acceptsGraphIso
    (fused (graph core2258) (root 9) 0 4) DegreeTwoThreeSpectrum3936.graph fusedMap2258=true := by decide +kernel
theorem certified2258 : Certified (graph core2258) (root 9) 0 4 :=
  of_native_maps core2258 DegreeTwoThreeSpectrum4328.graph DegreeTwoThreeSpectrum3936.graph
    sourceMap2258 fusedMap2258 sourceMap2258_checked fusedMap2258_checked
    DegreeTwoThreeFiniteComparisons.comparison2258
#print axioms sourceMap2258_checked
#print axioms fusedMap2258_checked
#print axioms certified2258
def sourceMap2258swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2258swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2258swap_checked : acceptsGraphIso
    (source (graph core2258) (root 9) 4 0) DegreeTwoThreeSpectrum4328.graph sourceMap2258swap=true := by decide +kernel
theorem fusedMap2258swap_checked : acceptsGraphIso
    (fused (graph core2258) (root 9) 4 0) DegreeTwoThreeSpectrum3936.graph fusedMap2258swap=true := by decide +kernel
theorem certified2258swap : Certified (graph core2258) (root 9) 4 0 :=
  of_native_maps core2258 DegreeTwoThreeSpectrum4328.graph DegreeTwoThreeSpectrum3936.graph
    sourceMap2258swap fusedMap2258swap sourceMap2258swap_checked fusedMap2258swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2258
#print axioms sourceMap2258swap_checked
#print axioms fusedMap2258swap_checked
#print axioms certified2258swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
