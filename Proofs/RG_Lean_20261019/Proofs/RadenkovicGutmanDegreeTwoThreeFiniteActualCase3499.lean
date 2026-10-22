/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3499 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap3499 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3499 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3499_checked : acceptsGraphIso
    (source (graph core3499) (root 6) 0 6) DegreeTwoThreeSpectrum2441.graph sourceMap3499=true := by decide +kernel
theorem fusedMap3499_checked : acceptsGraphIso
    (fused (graph core3499) (root 6) 0 6) DegreeTwoThreeSpectrum2444.graph fusedMap3499=true := by decide +kernel
theorem certified3499 : Certified (graph core3499) (root 6) 0 6 :=
  of_native_maps core3499 DegreeTwoThreeSpectrum2441.graph DegreeTwoThreeSpectrum2444.graph
    sourceMap3499 fusedMap3499 sourceMap3499_checked fusedMap3499_checked
    DegreeTwoThreeFiniteComparisons.comparison3499
#print axioms sourceMap3499_checked
#print axioms fusedMap3499_checked
#print axioms certified3499
def sourceMap3499swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3499swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3499swap_checked : acceptsGraphIso
    (source (graph core3499) (root 6) 6 0) DegreeTwoThreeSpectrum2441.graph sourceMap3499swap=true := by decide +kernel
theorem fusedMap3499swap_checked : acceptsGraphIso
    (fused (graph core3499) (root 6) 6 0) DegreeTwoThreeSpectrum2444.graph fusedMap3499swap=true := by decide +kernel
theorem certified3499swap : Certified (graph core3499) (root 6) 6 0 :=
  of_native_maps core3499 DegreeTwoThreeSpectrum2441.graph DegreeTwoThreeSpectrum2444.graph
    sourceMap3499swap fusedMap3499swap sourceMap3499swap_checked fusedMap3499swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3499
#print axioms sourceMap3499swap_checked
#print axioms fusedMap3499swap_checked
#print axioms certified3499swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
