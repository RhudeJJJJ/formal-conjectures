/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3366 : Family 9 := level9.get ⟨408,by decide⟩
def sourceMap3366 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3366 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3366_checked : acceptsGraphIso
    (source (graph core3366) (root 9) 0 5) DegreeTwoThreeSpectrum6434.graph sourceMap3366=true := by decide +kernel
theorem fusedMap3366_checked : acceptsGraphIso
    (fused (graph core3366) (root 9) 0 5) DegreeTwoThreeSpectrum5364.graph fusedMap3366=true := by decide +kernel
theorem certified3366 : Certified (graph core3366) (root 9) 0 5 :=
  of_native_maps core3366 DegreeTwoThreeSpectrum6434.graph DegreeTwoThreeSpectrum5364.graph
    sourceMap3366 fusedMap3366 sourceMap3366_checked fusedMap3366_checked
    DegreeTwoThreeFiniteComparisons.comparison3366
#print axioms sourceMap3366_checked
#print axioms fusedMap3366_checked
#print axioms certified3366
def sourceMap3366swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3366swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3366swap_checked : acceptsGraphIso
    (source (graph core3366) (root 9) 5 0) DegreeTwoThreeSpectrum6434.graph sourceMap3366swap=true := by decide +kernel
theorem fusedMap3366swap_checked : acceptsGraphIso
    (fused (graph core3366) (root 9) 5 0) DegreeTwoThreeSpectrum5364.graph fusedMap3366swap=true := by decide +kernel
theorem certified3366swap : Certified (graph core3366) (root 9) 5 0 :=
  of_native_maps core3366 DegreeTwoThreeSpectrum6434.graph DegreeTwoThreeSpectrum5364.graph
    sourceMap3366swap fusedMap3366swap sourceMap3366swap_checked fusedMap3366swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3366
#print axioms sourceMap3366swap_checked
#print axioms fusedMap3366swap_checked
#print axioms certified3366swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
