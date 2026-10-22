/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2425 : Family 9 := level9.get ⟨602,by decide⟩
def sourceMap2425 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2425 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2425_checked : acceptsGraphIso
    (source (graph core2425) (root 9) 0 4) DegreeTwoThreeSpectrum4736.graph sourceMap2425=true := by decide +kernel
theorem fusedMap2425_checked : acceptsGraphIso
    (fused (graph core2425) (root 9) 0 4) DegreeTwoThreeSpectrum4287.graph fusedMap2425=true := by decide +kernel
theorem certified2425 : Certified (graph core2425) (root 9) 0 4 :=
  of_native_maps core2425 DegreeTwoThreeSpectrum4736.graph DegreeTwoThreeSpectrum4287.graph
    sourceMap2425 fusedMap2425 sourceMap2425_checked fusedMap2425_checked
    DegreeTwoThreeFiniteComparisons.comparison2425
#print axioms sourceMap2425_checked
#print axioms fusedMap2425_checked
#print axioms certified2425
def sourceMap2425swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2425swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2425swap_checked : acceptsGraphIso
    (source (graph core2425) (root 9) 4 0) DegreeTwoThreeSpectrum4736.graph sourceMap2425swap=true := by decide +kernel
theorem fusedMap2425swap_checked : acceptsGraphIso
    (fused (graph core2425) (root 9) 4 0) DegreeTwoThreeSpectrum4287.graph fusedMap2425swap=true := by decide +kernel
theorem certified2425swap : Certified (graph core2425) (root 9) 4 0 :=
  of_native_maps core2425 DegreeTwoThreeSpectrum4736.graph DegreeTwoThreeSpectrum4287.graph
    sourceMap2425swap fusedMap2425swap sourceMap2425swap_checked fusedMap2425swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2425
#print axioms sourceMap2425swap_checked
#print axioms fusedMap2425swap_checked
#print axioms certified2425swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
