/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2883 : Family 10 := level10.get ⟨1281,by decide⟩
def sourceMap2883 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2883 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2883_checked : acceptsGraphIso
    (source (graph core2883) (root 10) 0 4) DegreeTwoThreeSpectrum6546.graph sourceMap2883=true := by decide +kernel
theorem fusedMap2883_checked : acceptsGraphIso
    (fused (graph core2883) (root 10) 0 4) DegreeTwoThreeSpectrum6547.graph fusedMap2883=true := by decide +kernel
theorem certified2883 : Certified (graph core2883) (root 10) 0 4 :=
  of_native_maps core2883 DegreeTwoThreeSpectrum6546.graph DegreeTwoThreeSpectrum6547.graph
    sourceMap2883 fusedMap2883 sourceMap2883_checked fusedMap2883_checked
    DegreeTwoThreeFiniteComparisons.comparison2883
#print axioms sourceMap2883_checked
#print axioms fusedMap2883_checked
#print axioms certified2883
def sourceMap2883swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2883swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2883swap_checked : acceptsGraphIso
    (source (graph core2883) (root 10) 4 0) DegreeTwoThreeSpectrum6546.graph sourceMap2883swap=true := by decide +kernel
theorem fusedMap2883swap_checked : acceptsGraphIso
    (fused (graph core2883) (root 10) 4 0) DegreeTwoThreeSpectrum6547.graph fusedMap2883swap=true := by decide +kernel
theorem certified2883swap : Certified (graph core2883) (root 10) 4 0 :=
  of_native_maps core2883 DegreeTwoThreeSpectrum6546.graph DegreeTwoThreeSpectrum6547.graph
    sourceMap2883swap fusedMap2883swap sourceMap2883swap_checked fusedMap2883swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2883
#print axioms sourceMap2883swap_checked
#print axioms fusedMap2883swap_checked
#print axioms certified2883swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
