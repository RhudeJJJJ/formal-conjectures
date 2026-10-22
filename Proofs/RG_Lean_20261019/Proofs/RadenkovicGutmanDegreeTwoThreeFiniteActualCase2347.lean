/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2347 : Family 9 := level9.get ⟨417,by decide⟩
def sourceMap2347 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2347 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2347_checked : acceptsGraphIso
    (source (graph core2347) (root 9) 0 4) DegreeTwoThreeSpectrum4395.graph sourceMap2347=true := by decide +kernel
theorem fusedMap2347_checked : acceptsGraphIso
    (fused (graph core2347) (root 9) 0 4) DegreeTwoThreeSpectrum4396.graph fusedMap2347=true := by decide +kernel
theorem certified2347 : Certified (graph core2347) (root 9) 0 4 :=
  of_native_maps core2347 DegreeTwoThreeSpectrum4395.graph DegreeTwoThreeSpectrum4396.graph
    sourceMap2347 fusedMap2347 sourceMap2347_checked fusedMap2347_checked
    DegreeTwoThreeFiniteComparisons.comparison2347
#print axioms sourceMap2347_checked
#print axioms fusedMap2347_checked
#print axioms certified2347
def sourceMap2347swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2347swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2347swap_checked : acceptsGraphIso
    (source (graph core2347) (root 9) 4 0) DegreeTwoThreeSpectrum4395.graph sourceMap2347swap=true := by decide +kernel
theorem fusedMap2347swap_checked : acceptsGraphIso
    (fused (graph core2347) (root 9) 4 0) DegreeTwoThreeSpectrum4396.graph fusedMap2347swap=true := by decide +kernel
theorem certified2347swap : Certified (graph core2347) (root 9) 4 0 :=
  of_native_maps core2347 DegreeTwoThreeSpectrum4395.graph DegreeTwoThreeSpectrum4396.graph
    sourceMap2347swap fusedMap2347swap sourceMap2347swap_checked fusedMap2347swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2347
#print axioms sourceMap2347swap_checked
#print axioms fusedMap2347swap_checked
#print axioms certified2347swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
