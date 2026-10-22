/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2304 : Family 9 := level9.get ⟨304,by decide⟩
def sourceMap2304 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 9 0 4 v)
def fusedMap2304 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2304_checked : acceptsGraphIso
    (source (graph core2304) (root 9) 0 4) DegreeTwoThreeSpectrum4655.graph sourceMap2304=true := by decide +kernel
theorem fusedMap2304_checked : acceptsGraphIso
    (fused (graph core2304) (root 9) 0 4) DegreeTwoThreeSpectrum4139.graph fusedMap2304=true := by decide +kernel
theorem certified2304 : Certified (graph core2304) (root 9) 0 4 :=
  of_native_maps core2304 DegreeTwoThreeSpectrum4655.graph DegreeTwoThreeSpectrum4139.graph
    sourceMap2304 fusedMap2304 sourceMap2304_checked fusedMap2304_checked
    DegreeTwoThreeFiniteComparisons.comparison2304
#print axioms sourceMap2304_checked
#print axioms fusedMap2304_checked
#print axioms certified2304
def sourceMap2304swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11,15] (sourceLabel 9 4 0 v)
def fusedMap2304swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2304swap_checked : acceptsGraphIso
    (source (graph core2304) (root 9) 4 0) DegreeTwoThreeSpectrum4655.graph sourceMap2304swap=true := by decide +kernel
theorem fusedMap2304swap_checked : acceptsGraphIso
    (fused (graph core2304) (root 9) 4 0) DegreeTwoThreeSpectrum4139.graph fusedMap2304swap=true := by decide +kernel
theorem certified2304swap : Certified (graph core2304) (root 9) 4 0 :=
  of_native_maps core2304 DegreeTwoThreeSpectrum4655.graph DegreeTwoThreeSpectrum4139.graph
    sourceMap2304swap fusedMap2304swap sourceMap2304swap_checked fusedMap2304swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2304
#print axioms sourceMap2304swap_checked
#print axioms fusedMap2304swap_checked
#print axioms certified2304swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
