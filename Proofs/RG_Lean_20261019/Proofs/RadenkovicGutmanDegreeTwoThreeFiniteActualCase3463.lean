/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3463 : Family 9 := level9.get ⟨650,by decide⟩
def sourceMap3463 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3463 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3463_checked : acceptsGraphIso
    (source (graph core3463) (root 9) 0 5) DegreeTwoThreeSpectrum6582.graph sourceMap3463=true := by decide +kernel
theorem fusedMap3463_checked : acceptsGraphIso
    (fused (graph core3463) (root 9) 0 5) DegreeTwoThreeSpectrum6583.graph fusedMap3463=true := by decide +kernel
theorem certified3463 : Certified (graph core3463) (root 9) 0 5 :=
  of_native_maps core3463 DegreeTwoThreeSpectrum6582.graph DegreeTwoThreeSpectrum6583.graph
    sourceMap3463 fusedMap3463 sourceMap3463_checked fusedMap3463_checked
    DegreeTwoThreeFiniteComparisons.comparison3463
#print axioms sourceMap3463_checked
#print axioms fusedMap3463_checked
#print axioms certified3463
def sourceMap3463swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3463swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3463swap_checked : acceptsGraphIso
    (source (graph core3463) (root 9) 5 0) DegreeTwoThreeSpectrum6582.graph sourceMap3463swap=true := by decide +kernel
theorem fusedMap3463swap_checked : acceptsGraphIso
    (fused (graph core3463) (root 9) 5 0) DegreeTwoThreeSpectrum6583.graph fusedMap3463swap=true := by decide +kernel
theorem certified3463swap : Certified (graph core3463) (root 9) 5 0 :=
  of_native_maps core3463 DegreeTwoThreeSpectrum6582.graph DegreeTwoThreeSpectrum6583.graph
    sourceMap3463swap fusedMap3463swap sourceMap3463swap_checked fusedMap3463swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3463
#print axioms sourceMap3463swap_checked
#print axioms fusedMap3463swap_checked
#print axioms certified3463swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
