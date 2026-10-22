/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2804 : Family 10 := level10.get ⟨1085,by decide⟩
def sourceMap2804 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2804 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2804_checked : acceptsGraphIso
    (source (graph core2804) (root 10) 0 4) DegreeTwoThreeSpectrum6152.graph sourceMap2804=true := by decide +kernel
theorem fusedMap2804_checked : acceptsGraphIso
    (fused (graph core2804) (root 10) 0 4) DegreeTwoThreeSpectrum6153.graph fusedMap2804=true := by decide +kernel
theorem certified2804 : Certified (graph core2804) (root 10) 0 4 :=
  of_native_maps core2804 DegreeTwoThreeSpectrum6152.graph DegreeTwoThreeSpectrum6153.graph
    sourceMap2804 fusedMap2804 sourceMap2804_checked fusedMap2804_checked
    DegreeTwoThreeFiniteComparisons.comparison2804
#print axioms sourceMap2804_checked
#print axioms fusedMap2804_checked
#print axioms certified2804
def sourceMap2804swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2804swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2804swap_checked : acceptsGraphIso
    (source (graph core2804) (root 10) 4 0) DegreeTwoThreeSpectrum6152.graph sourceMap2804swap=true := by decide +kernel
theorem fusedMap2804swap_checked : acceptsGraphIso
    (fused (graph core2804) (root 10) 4 0) DegreeTwoThreeSpectrum6153.graph fusedMap2804swap=true := by decide +kernel
theorem certified2804swap : Certified (graph core2804) (root 10) 4 0 :=
  of_native_maps core2804 DegreeTwoThreeSpectrum6152.graph DegreeTwoThreeSpectrum6153.graph
    sourceMap2804swap fusedMap2804swap sourceMap2804swap_checked fusedMap2804swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2804
#print axioms sourceMap2804swap_checked
#print axioms fusedMap2804swap_checked
#print axioms certified2804swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
