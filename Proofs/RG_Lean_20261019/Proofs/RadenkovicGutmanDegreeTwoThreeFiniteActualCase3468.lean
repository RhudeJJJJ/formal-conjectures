/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3468 : Family 9 := level9.get ⟨659,by decide⟩
def sourceMap3468 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3468 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3468_checked : acceptsGraphIso
    (source (graph core3468) (root 9) 0 5) DegreeTwoThreeSpectrum6628.graph sourceMap3468=true := by decide +kernel
theorem fusedMap3468_checked : acceptsGraphIso
    (fused (graph core3468) (root 9) 0 5) DegreeTwoThreeSpectrum6629.graph fusedMap3468=true := by decide +kernel
theorem certified3468 : Certified (graph core3468) (root 9) 0 5 :=
  of_native_maps core3468 DegreeTwoThreeSpectrum6628.graph DegreeTwoThreeSpectrum6629.graph
    sourceMap3468 fusedMap3468 sourceMap3468_checked fusedMap3468_checked
    DegreeTwoThreeFiniteComparisons.comparison3468
#print axioms sourceMap3468_checked
#print axioms fusedMap3468_checked
#print axioms certified3468
def sourceMap3468swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3468swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3468swap_checked : acceptsGraphIso
    (source (graph core3468) (root 9) 5 0) DegreeTwoThreeSpectrum6628.graph sourceMap3468swap=true := by decide +kernel
theorem fusedMap3468swap_checked : acceptsGraphIso
    (fused (graph core3468) (root 9) 5 0) DegreeTwoThreeSpectrum6629.graph fusedMap3468swap=true := by decide +kernel
theorem certified3468swap : Certified (graph core3468) (root 9) 5 0 :=
  of_native_maps core3468 DegreeTwoThreeSpectrum6628.graph DegreeTwoThreeSpectrum6629.graph
    sourceMap3468swap fusedMap3468swap sourceMap3468swap_checked fusedMap3468swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3468
#print axioms sourceMap3468swap_checked
#print axioms fusedMap3468swap_checked
#print axioms certified3468swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
