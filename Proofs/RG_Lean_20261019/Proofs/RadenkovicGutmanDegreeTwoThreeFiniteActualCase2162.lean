/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2162 : Family 8 := level8.get ⟨146,by decide⟩
def sourceMap2162 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2162 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2162_checked : acceptsGraphIso
    (source (graph core2162) (root 8) 0 4) DegreeTwoThreeSpectrum2709.graph sourceMap2162=true := by decide +kernel
theorem fusedMap2162_checked : acceptsGraphIso
    (fused (graph core2162) (root 8) 0 4) DegreeTwoThreeSpectrum2711.graph fusedMap2162=true := by decide +kernel
theorem certified2162 : Certified (graph core2162) (root 8) 0 4 :=
  of_native_maps core2162 DegreeTwoThreeSpectrum2709.graph DegreeTwoThreeSpectrum2711.graph
    sourceMap2162 fusedMap2162 sourceMap2162_checked fusedMap2162_checked
    DegreeTwoThreeFiniteComparisons.comparison2162
#print axioms sourceMap2162_checked
#print axioms fusedMap2162_checked
#print axioms certified2162
def sourceMap2162swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2162swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2162swap_checked : acceptsGraphIso
    (source (graph core2162) (root 8) 4 0) DegreeTwoThreeSpectrum2709.graph sourceMap2162swap=true := by decide +kernel
theorem fusedMap2162swap_checked : acceptsGraphIso
    (fused (graph core2162) (root 8) 4 0) DegreeTwoThreeSpectrum2711.graph fusedMap2162swap=true := by decide +kernel
theorem certified2162swap : Certified (graph core2162) (root 8) 4 0 :=
  of_native_maps core2162 DegreeTwoThreeSpectrum2709.graph DegreeTwoThreeSpectrum2711.graph
    sourceMap2162swap fusedMap2162swap sourceMap2162swap_checked fusedMap2162swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2162
#print axioms sourceMap2162swap_checked
#print axioms fusedMap2162swap_checked
#print axioms certified2162swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
