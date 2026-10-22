/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3450 : Family 9 := level9.get ⟨609,by decide⟩
def sourceMap3450 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3450 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3450_checked : acceptsGraphIso
    (source (graph core3450) (root 9) 0 5) DegreeTwoThreeSpectrum6283.graph sourceMap3450=true := by decide +kernel
theorem fusedMap3450_checked : acceptsGraphIso
    (fused (graph core3450) (root 9) 0 5) DegreeTwoThreeSpectrum6284.graph fusedMap3450=true := by decide +kernel
theorem certified3450 : Certified (graph core3450) (root 9) 0 5 :=
  of_native_maps core3450 DegreeTwoThreeSpectrum6283.graph DegreeTwoThreeSpectrum6284.graph
    sourceMap3450 fusedMap3450 sourceMap3450_checked fusedMap3450_checked
    DegreeTwoThreeFiniteComparisons.comparison3450
#print axioms sourceMap3450_checked
#print axioms fusedMap3450_checked
#print axioms certified3450
def sourceMap3450swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3450swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3450swap_checked : acceptsGraphIso
    (source (graph core3450) (root 9) 5 0) DegreeTwoThreeSpectrum6283.graph sourceMap3450swap=true := by decide +kernel
theorem fusedMap3450swap_checked : acceptsGraphIso
    (fused (graph core3450) (root 9) 5 0) DegreeTwoThreeSpectrum6284.graph fusedMap3450swap=true := by decide +kernel
theorem certified3450swap : Certified (graph core3450) (root 9) 5 0 :=
  of_native_maps core3450 DegreeTwoThreeSpectrum6283.graph DegreeTwoThreeSpectrum6284.graph
    sourceMap3450swap fusedMap3450swap sourceMap3450swap_checked fusedMap3450swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3450
#print axioms sourceMap3450swap_checked
#print axioms fusedMap3450swap_checked
#print axioms certified3450swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
