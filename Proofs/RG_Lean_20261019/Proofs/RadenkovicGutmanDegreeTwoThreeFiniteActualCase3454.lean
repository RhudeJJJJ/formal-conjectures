/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3454 : Family 9 := level9.get ⟨622,by decide⟩
def sourceMap3454 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3454 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3454_checked : acceptsGraphIso
    (source (graph core3454) (root 9) 0 5) DegreeTwoThreeSpectrum6357.graph sourceMap3454=true := by decide +kernel
theorem fusedMap3454_checked : acceptsGraphIso
    (fused (graph core3454) (root 9) 0 5) DegreeTwoThreeSpectrum6358.graph fusedMap3454=true := by decide +kernel
theorem certified3454 : Certified (graph core3454) (root 9) 0 5 :=
  of_native_maps core3454 DegreeTwoThreeSpectrum6357.graph DegreeTwoThreeSpectrum6358.graph
    sourceMap3454 fusedMap3454 sourceMap3454_checked fusedMap3454_checked
    DegreeTwoThreeFiniteComparisons.comparison3454
#print axioms sourceMap3454_checked
#print axioms fusedMap3454_checked
#print axioms certified3454
def sourceMap3454swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3454swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3454swap_checked : acceptsGraphIso
    (source (graph core3454) (root 9) 5 0) DegreeTwoThreeSpectrum6357.graph sourceMap3454swap=true := by decide +kernel
theorem fusedMap3454swap_checked : acceptsGraphIso
    (fused (graph core3454) (root 9) 5 0) DegreeTwoThreeSpectrum6358.graph fusedMap3454swap=true := by decide +kernel
theorem certified3454swap : Certified (graph core3454) (root 9) 5 0 :=
  of_native_maps core3454 DegreeTwoThreeSpectrum6357.graph DegreeTwoThreeSpectrum6358.graph
    sourceMap3454swap fusedMap3454swap sourceMap3454swap_checked fusedMap3454swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3454
#print axioms sourceMap3454swap_checked
#print axioms fusedMap3454swap_checked
#print axioms certified3454swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
