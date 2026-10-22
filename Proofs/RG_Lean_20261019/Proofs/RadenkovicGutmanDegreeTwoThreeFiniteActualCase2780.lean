/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2780 : Family 10 := level10.get ⟨1025,by decide⟩
def sourceMap2780 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2780 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2780_checked : acceptsGraphIso
    (source (graph core2780) (root 10) 0 4) DegreeTwoThreeSpectrum6031.graph sourceMap2780=true := by decide +kernel
theorem fusedMap2780_checked : acceptsGraphIso
    (fused (graph core2780) (root 10) 0 4) DegreeTwoThreeSpectrum6032.graph fusedMap2780=true := by decide +kernel
theorem certified2780 : Certified (graph core2780) (root 10) 0 4 :=
  of_native_maps core2780 DegreeTwoThreeSpectrum6031.graph DegreeTwoThreeSpectrum6032.graph
    sourceMap2780 fusedMap2780 sourceMap2780_checked fusedMap2780_checked
    DegreeTwoThreeFiniteComparisons.comparison2780
#print axioms sourceMap2780_checked
#print axioms fusedMap2780_checked
#print axioms certified2780
def sourceMap2780swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2780swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2780swap_checked : acceptsGraphIso
    (source (graph core2780) (root 10) 4 0) DegreeTwoThreeSpectrum6031.graph sourceMap2780swap=true := by decide +kernel
theorem fusedMap2780swap_checked : acceptsGraphIso
    (fused (graph core2780) (root 10) 4 0) DegreeTwoThreeSpectrum6032.graph fusedMap2780swap=true := by decide +kernel
theorem certified2780swap : Certified (graph core2780) (root 10) 4 0 :=
  of_native_maps core2780 DegreeTwoThreeSpectrum6031.graph DegreeTwoThreeSpectrum6032.graph
    sourceMap2780swap fusedMap2780swap sourceMap2780swap_checked fusedMap2780swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2780
#print axioms sourceMap2780swap_checked
#print axioms fusedMap2780swap_checked
#print axioms certified2780swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
