/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3452 : Family 9 := level9.get ⟨617,by decide⟩
def sourceMap3452 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3452 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3452_checked : acceptsGraphIso
    (source (graph core3452) (root 9) 0 5) DegreeTwoThreeSpectrum6339.graph sourceMap3452=true := by decide +kernel
theorem fusedMap3452_checked : acceptsGraphIso
    (fused (graph core3452) (root 9) 0 5) DegreeTwoThreeSpectrum6340.graph fusedMap3452=true := by decide +kernel
theorem certified3452 : Certified (graph core3452) (root 9) 0 5 :=
  of_native_maps core3452 DegreeTwoThreeSpectrum6339.graph DegreeTwoThreeSpectrum6340.graph
    sourceMap3452 fusedMap3452 sourceMap3452_checked fusedMap3452_checked
    DegreeTwoThreeFiniteComparisons.comparison3452
#print axioms sourceMap3452_checked
#print axioms fusedMap3452_checked
#print axioms certified3452
def sourceMap3452swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3452swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3452swap_checked : acceptsGraphIso
    (source (graph core3452) (root 9) 5 0) DegreeTwoThreeSpectrum6339.graph sourceMap3452swap=true := by decide +kernel
theorem fusedMap3452swap_checked : acceptsGraphIso
    (fused (graph core3452) (root 9) 5 0) DegreeTwoThreeSpectrum6340.graph fusedMap3452swap=true := by decide +kernel
theorem certified3452swap : Certified (graph core3452) (root 9) 5 0 :=
  of_native_maps core3452 DegreeTwoThreeSpectrum6339.graph DegreeTwoThreeSpectrum6340.graph
    sourceMap3452swap fusedMap3452swap sourceMap3452swap_checked fusedMap3452swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3452
#print axioms sourceMap3452swap_checked
#print axioms fusedMap3452swap_checked
#print axioms certified3452swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
