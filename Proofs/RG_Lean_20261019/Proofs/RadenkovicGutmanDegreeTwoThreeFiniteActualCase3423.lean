/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3423 : Family 9 := level9.get ⟨552,by decide⟩
def sourceMap3423 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3423 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3423_checked : acceptsGraphIso
    (source (graph core3423) (root 9) 0 5) DegreeTwoThreeSpectrum6000.graph sourceMap3423=true := by decide +kernel
theorem fusedMap3423_checked : acceptsGraphIso
    (fused (graph core3423) (root 9) 0 5) DegreeTwoThreeSpectrum6001.graph fusedMap3423=true := by decide +kernel
theorem certified3423 : Certified (graph core3423) (root 9) 0 5 :=
  of_native_maps core3423 DegreeTwoThreeSpectrum6000.graph DegreeTwoThreeSpectrum6001.graph
    sourceMap3423 fusedMap3423 sourceMap3423_checked fusedMap3423_checked
    DegreeTwoThreeFiniteComparisons.comparison3423
#print axioms sourceMap3423_checked
#print axioms fusedMap3423_checked
#print axioms certified3423
def sourceMap3423swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3423swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3423swap_checked : acceptsGraphIso
    (source (graph core3423) (root 9) 5 0) DegreeTwoThreeSpectrum6000.graph sourceMap3423swap=true := by decide +kernel
theorem fusedMap3423swap_checked : acceptsGraphIso
    (fused (graph core3423) (root 9) 5 0) DegreeTwoThreeSpectrum6001.graph fusedMap3423swap=true := by decide +kernel
theorem certified3423swap : Certified (graph core3423) (root 9) 5 0 :=
  of_native_maps core3423 DegreeTwoThreeSpectrum6000.graph DegreeTwoThreeSpectrum6001.graph
    sourceMap3423swap fusedMap3423swap sourceMap3423swap_checked fusedMap3423swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3423
#print axioms sourceMap3423swap_checked
#print axioms fusedMap3423swap_checked
#print axioms certified3423swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
