/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2289 : Family 9 := level9.get ⟨265,by decide⟩
def sourceMap2289 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2289 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2289_checked : acceptsGraphIso
    (source (graph core2289) (root 9) 0 4) DegreeTwoThreeSpectrum4592.graph sourceMap2289=true := by decide +kernel
theorem fusedMap2289_checked : acceptsGraphIso
    (fused (graph core2289) (root 9) 0 4) DegreeTwoThreeSpectrum4076.graph fusedMap2289=true := by decide +kernel
theorem certified2289 : Certified (graph core2289) (root 9) 0 4 :=
  of_native_maps core2289 DegreeTwoThreeSpectrum4592.graph DegreeTwoThreeSpectrum4076.graph
    sourceMap2289 fusedMap2289 sourceMap2289_checked fusedMap2289_checked
    DegreeTwoThreeFiniteComparisons.comparison2289
#print axioms sourceMap2289_checked
#print axioms fusedMap2289_checked
#print axioms certified2289
def sourceMap2289swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2289swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2289swap_checked : acceptsGraphIso
    (source (graph core2289) (root 9) 4 0) DegreeTwoThreeSpectrum4592.graph sourceMap2289swap=true := by decide +kernel
theorem fusedMap2289swap_checked : acceptsGraphIso
    (fused (graph core2289) (root 9) 4 0) DegreeTwoThreeSpectrum4076.graph fusedMap2289swap=true := by decide +kernel
theorem certified2289swap : Certified (graph core2289) (root 9) 4 0 :=
  of_native_maps core2289 DegreeTwoThreeSpectrum4592.graph DegreeTwoThreeSpectrum4076.graph
    sourceMap2289swap fusedMap2289swap sourceMap2289swap_checked fusedMap2289swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2289
#print axioms sourceMap2289swap_checked
#print axioms fusedMap2289swap_checked
#print axioms certified2289swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
