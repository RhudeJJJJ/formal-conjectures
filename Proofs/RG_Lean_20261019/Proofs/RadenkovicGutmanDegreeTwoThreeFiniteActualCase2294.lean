/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2294 : Family 9 := level9.get ⟨280,by decide⟩
def sourceMap2294 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2294 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2294_checked : acceptsGraphIso
    (source (graph core2294) (root 9) 0 4) DegreeTwoThreeSpectrum4621.graph sourceMap2294=true := by decide +kernel
theorem fusedMap2294_checked : acceptsGraphIso
    (fused (graph core2294) (root 9) 0 4) DegreeTwoThreeSpectrum4097.graph fusedMap2294=true := by decide +kernel
theorem certified2294 : Certified (graph core2294) (root 9) 0 4 :=
  of_native_maps core2294 DegreeTwoThreeSpectrum4621.graph DegreeTwoThreeSpectrum4097.graph
    sourceMap2294 fusedMap2294 sourceMap2294_checked fusedMap2294_checked
    DegreeTwoThreeFiniteComparisons.comparison2294
#print axioms sourceMap2294_checked
#print axioms fusedMap2294_checked
#print axioms certified2294
def sourceMap2294swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2294swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2294swap_checked : acceptsGraphIso
    (source (graph core2294) (root 9) 4 0) DegreeTwoThreeSpectrum4621.graph sourceMap2294swap=true := by decide +kernel
theorem fusedMap2294swap_checked : acceptsGraphIso
    (fused (graph core2294) (root 9) 4 0) DegreeTwoThreeSpectrum4097.graph fusedMap2294swap=true := by decide +kernel
theorem certified2294swap : Certified (graph core2294) (root 9) 4 0 :=
  of_native_maps core2294 DegreeTwoThreeSpectrum4621.graph DegreeTwoThreeSpectrum4097.graph
    sourceMap2294swap fusedMap2294swap sourceMap2294swap_checked fusedMap2294swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2294
#print axioms sourceMap2294swap_checked
#print axioms fusedMap2294swap_checked
#print axioms certified2294swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
