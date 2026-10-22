/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2298 : Family 9 := level9.get ⟨291,by decide⟩
def sourceMap2298 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2298 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2298_checked : acceptsGraphIso
    (source (graph core2298) (root 9) 0 4) DegreeTwoThreeSpectrum4643.graph sourceMap2298=true := by decide +kernel
theorem fusedMap2298_checked : acceptsGraphIso
    (fused (graph core2298) (root 9) 0 4) DegreeTwoThreeSpectrum4119.graph fusedMap2298=true := by decide +kernel
theorem certified2298 : Certified (graph core2298) (root 9) 0 4 :=
  of_native_maps core2298 DegreeTwoThreeSpectrum4643.graph DegreeTwoThreeSpectrum4119.graph
    sourceMap2298 fusedMap2298 sourceMap2298_checked fusedMap2298_checked
    DegreeTwoThreeFiniteComparisons.comparison2298
#print axioms sourceMap2298_checked
#print axioms fusedMap2298_checked
#print axioms certified2298
def sourceMap2298swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2298swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2298swap_checked : acceptsGraphIso
    (source (graph core2298) (root 9) 4 0) DegreeTwoThreeSpectrum4643.graph sourceMap2298swap=true := by decide +kernel
theorem fusedMap2298swap_checked : acceptsGraphIso
    (fused (graph core2298) (root 9) 4 0) DegreeTwoThreeSpectrum4119.graph fusedMap2298swap=true := by decide +kernel
theorem certified2298swap : Certified (graph core2298) (root 9) 4 0 :=
  of_native_maps core2298 DegreeTwoThreeSpectrum4643.graph DegreeTwoThreeSpectrum4119.graph
    sourceMap2298swap fusedMap2298swap sourceMap2298swap_checked fusedMap2298swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2298
#print axioms sourceMap2298swap_checked
#print axioms fusedMap2298swap_checked
#print axioms certified2298swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
