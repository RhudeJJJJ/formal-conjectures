/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2277 : Family 9 := level9.get ⟨233,by decide⟩
def sourceMap2277 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2277 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2277_checked : acceptsGraphIso
    (source (graph core2277) (root 9) 0 4) DegreeTwoThreeSpectrum4506.graph sourceMap2277=true := by decide +kernel
theorem fusedMap2277_checked : acceptsGraphIso
    (fused (graph core2277) (root 9) 0 4) DegreeTwoThreeSpectrum4025.graph fusedMap2277=true := by decide +kernel
theorem certified2277 : Certified (graph core2277) (root 9) 0 4 :=
  of_native_maps core2277 DegreeTwoThreeSpectrum4506.graph DegreeTwoThreeSpectrum4025.graph
    sourceMap2277 fusedMap2277 sourceMap2277_checked fusedMap2277_checked
    DegreeTwoThreeFiniteComparisons.comparison2277
#print axioms sourceMap2277_checked
#print axioms fusedMap2277_checked
#print axioms certified2277
def sourceMap2277swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2277swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2277swap_checked : acceptsGraphIso
    (source (graph core2277) (root 9) 4 0) DegreeTwoThreeSpectrum4506.graph sourceMap2277swap=true := by decide +kernel
theorem fusedMap2277swap_checked : acceptsGraphIso
    (fused (graph core2277) (root 9) 4 0) DegreeTwoThreeSpectrum4025.graph fusedMap2277swap=true := by decide +kernel
theorem certified2277swap : Certified (graph core2277) (root 9) 4 0 :=
  of_native_maps core2277 DegreeTwoThreeSpectrum4506.graph DegreeTwoThreeSpectrum4025.graph
    sourceMap2277swap fusedMap2277swap sourceMap2277swap_checked fusedMap2277swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2277
#print axioms sourceMap2277swap_checked
#print axioms fusedMap2277swap_checked
#print axioms certified2277swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
