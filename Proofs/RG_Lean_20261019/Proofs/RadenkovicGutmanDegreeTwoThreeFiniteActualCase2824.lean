/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2824 : Family 10 := level10.get ⟨1139,by decide⟩
def sourceMap2824 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2824 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2824_checked : acceptsGraphIso
    (source (graph core2824) (root 10) 0 4) DegreeTwoThreeSpectrum6264.graph sourceMap2824=true := by decide +kernel
theorem fusedMap2824_checked : acceptsGraphIso
    (fused (graph core2824) (root 10) 0 4) DegreeTwoThreeSpectrum6265.graph fusedMap2824=true := by decide +kernel
theorem certified2824 : Certified (graph core2824) (root 10) 0 4 :=
  of_native_maps core2824 DegreeTwoThreeSpectrum6264.graph DegreeTwoThreeSpectrum6265.graph
    sourceMap2824 fusedMap2824 sourceMap2824_checked fusedMap2824_checked
    DegreeTwoThreeFiniteComparisons.comparison2824
#print axioms sourceMap2824_checked
#print axioms fusedMap2824_checked
#print axioms certified2824
def sourceMap2824swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2824swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2824swap_checked : acceptsGraphIso
    (source (graph core2824) (root 10) 4 0) DegreeTwoThreeSpectrum6264.graph sourceMap2824swap=true := by decide +kernel
theorem fusedMap2824swap_checked : acceptsGraphIso
    (fused (graph core2824) (root 10) 4 0) DegreeTwoThreeSpectrum6265.graph fusedMap2824swap=true := by decide +kernel
theorem certified2824swap : Certified (graph core2824) (root 10) 4 0 :=
  of_native_maps core2824 DegreeTwoThreeSpectrum6264.graph DegreeTwoThreeSpectrum6265.graph
    sourceMap2824swap fusedMap2824swap sourceMap2824swap_checked fusedMap2824swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2824
#print axioms sourceMap2824swap_checked
#print axioms fusedMap2824swap_checked
#print axioms certified2824swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
