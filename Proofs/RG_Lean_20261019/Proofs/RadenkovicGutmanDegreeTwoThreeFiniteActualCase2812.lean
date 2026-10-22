/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2812 : Family 10 := level10.get ⟨1108,by decide⟩
def sourceMap2812 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2812 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2812_checked : acceptsGraphIso
    (source (graph core2812) (root 10) 0 4) DegreeTwoThreeSpectrum6200.graph sourceMap2812=true := by decide +kernel
theorem fusedMap2812_checked : acceptsGraphIso
    (fused (graph core2812) (root 10) 0 4) DegreeTwoThreeSpectrum6201.graph fusedMap2812=true := by decide +kernel
theorem certified2812 : Certified (graph core2812) (root 10) 0 4 :=
  of_native_maps core2812 DegreeTwoThreeSpectrum6200.graph DegreeTwoThreeSpectrum6201.graph
    sourceMap2812 fusedMap2812 sourceMap2812_checked fusedMap2812_checked
    DegreeTwoThreeFiniteComparisons.comparison2812
#print axioms sourceMap2812_checked
#print axioms fusedMap2812_checked
#print axioms certified2812
def sourceMap2812swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2812swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2812swap_checked : acceptsGraphIso
    (source (graph core2812) (root 10) 4 0) DegreeTwoThreeSpectrum6200.graph sourceMap2812swap=true := by decide +kernel
theorem fusedMap2812swap_checked : acceptsGraphIso
    (fused (graph core2812) (root 10) 4 0) DegreeTwoThreeSpectrum6201.graph fusedMap2812swap=true := by decide +kernel
theorem certified2812swap : Certified (graph core2812) (root 10) 4 0 :=
  of_native_maps core2812 DegreeTwoThreeSpectrum6200.graph DegreeTwoThreeSpectrum6201.graph
    sourceMap2812swap fusedMap2812swap sourceMap2812swap_checked fusedMap2812swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2812
#print axioms sourceMap2812swap_checked
#print axioms fusedMap2812swap_checked
#print axioms certified2812swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
