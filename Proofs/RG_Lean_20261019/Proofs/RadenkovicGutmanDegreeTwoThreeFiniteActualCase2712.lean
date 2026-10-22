/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2712 : Family 10 := level10.get ⟨854,by decide⟩
def sourceMap2712 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2712 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2712_checked : acceptsGraphIso
    (source (graph core2712) (root 10) 0 4) DegreeTwoThreeSpectrum6901.graph sourceMap2712=true := by decide +kernel
theorem fusedMap2712_checked : acceptsGraphIso
    (fused (graph core2712) (root 10) 0 4) DegreeTwoThreeSpectrum5690.graph fusedMap2712=true := by decide +kernel
theorem certified2712 : Certified (graph core2712) (root 10) 0 4 :=
  of_native_maps core2712 DegreeTwoThreeSpectrum6901.graph DegreeTwoThreeSpectrum5690.graph
    sourceMap2712 fusedMap2712 sourceMap2712_checked fusedMap2712_checked
    DegreeTwoThreeFiniteComparisons.comparison2712
#print axioms sourceMap2712_checked
#print axioms fusedMap2712_checked
#print axioms certified2712
def sourceMap2712swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2712swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2712swap_checked : acceptsGraphIso
    (source (graph core2712) (root 10) 4 0) DegreeTwoThreeSpectrum6901.graph sourceMap2712swap=true := by decide +kernel
theorem fusedMap2712swap_checked : acceptsGraphIso
    (fused (graph core2712) (root 10) 4 0) DegreeTwoThreeSpectrum5690.graph fusedMap2712swap=true := by decide +kernel
theorem certified2712swap : Certified (graph core2712) (root 10) 4 0 :=
  of_native_maps core2712 DegreeTwoThreeSpectrum6901.graph DegreeTwoThreeSpectrum5690.graph
    sourceMap2712swap fusedMap2712swap sourceMap2712swap_checked fusedMap2712swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2712
#print axioms sourceMap2712swap_checked
#print axioms fusedMap2712swap_checked
#print axioms certified2712swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
