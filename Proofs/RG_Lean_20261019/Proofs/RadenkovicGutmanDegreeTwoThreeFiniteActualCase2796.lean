/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2796 : Family 10 := level10.get ⟨1068,by decide⟩
def sourceMap2796 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2796 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2796_checked : acceptsGraphIso
    (source (graph core2796) (root 10) 0 4) DegreeTwoThreeSpectrum6124.graph sourceMap2796=true := by decide +kernel
theorem fusedMap2796_checked : acceptsGraphIso
    (fused (graph core2796) (root 10) 0 4) DegreeTwoThreeSpectrum6125.graph fusedMap2796=true := by decide +kernel
theorem certified2796 : Certified (graph core2796) (root 10) 0 4 :=
  of_native_maps core2796 DegreeTwoThreeSpectrum6124.graph DegreeTwoThreeSpectrum6125.graph
    sourceMap2796 fusedMap2796 sourceMap2796_checked fusedMap2796_checked
    DegreeTwoThreeFiniteComparisons.comparison2796
#print axioms sourceMap2796_checked
#print axioms fusedMap2796_checked
#print axioms certified2796
def sourceMap2796swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2796swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2796swap_checked : acceptsGraphIso
    (source (graph core2796) (root 10) 4 0) DegreeTwoThreeSpectrum6124.graph sourceMap2796swap=true := by decide +kernel
theorem fusedMap2796swap_checked : acceptsGraphIso
    (fused (graph core2796) (root 10) 4 0) DegreeTwoThreeSpectrum6125.graph fusedMap2796swap=true := by decide +kernel
theorem certified2796swap : Certified (graph core2796) (root 10) 4 0 :=
  of_native_maps core2796 DegreeTwoThreeSpectrum6124.graph DegreeTwoThreeSpectrum6125.graph
    sourceMap2796swap fusedMap2796swap sourceMap2796swap_checked fusedMap2796swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2796
#print axioms sourceMap2796swap_checked
#print axioms fusedMap2796swap_checked
#print axioms certified2796swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
