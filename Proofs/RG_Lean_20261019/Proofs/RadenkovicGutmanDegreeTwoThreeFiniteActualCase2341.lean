/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2341 : Family 9 := level9.get ⟨402,by decide⟩
def sourceMap2341 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2341 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2341_checked : acceptsGraphIso
    (source (graph core2341) (root 9) 0 4) DegreeTwoThreeSpectrum4359.graph sourceMap2341=true := by decide +kernel
theorem fusedMap2341_checked : acceptsGraphIso
    (fused (graph core2341) (root 9) 0 4) DegreeTwoThreeSpectrum4360.graph fusedMap2341=true := by decide +kernel
theorem certified2341 : Certified (graph core2341) (root 9) 0 4 :=
  of_native_maps core2341 DegreeTwoThreeSpectrum4359.graph DegreeTwoThreeSpectrum4360.graph
    sourceMap2341 fusedMap2341 sourceMap2341_checked fusedMap2341_checked
    DegreeTwoThreeFiniteComparisons.comparison2341
#print axioms sourceMap2341_checked
#print axioms fusedMap2341_checked
#print axioms certified2341
def sourceMap2341swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2341swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2341swap_checked : acceptsGraphIso
    (source (graph core2341) (root 9) 4 0) DegreeTwoThreeSpectrum4359.graph sourceMap2341swap=true := by decide +kernel
theorem fusedMap2341swap_checked : acceptsGraphIso
    (fused (graph core2341) (root 9) 4 0) DegreeTwoThreeSpectrum4360.graph fusedMap2341swap=true := by decide +kernel
theorem certified2341swap : Certified (graph core2341) (root 9) 4 0 :=
  of_native_maps core2341 DegreeTwoThreeSpectrum4359.graph DegreeTwoThreeSpectrum4360.graph
    sourceMap2341swap fusedMap2341swap sourceMap2341swap_checked fusedMap2341swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2341
#print axioms sourceMap2341swap_checked
#print axioms fusedMap2341swap_checked
#print axioms certified2341swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
