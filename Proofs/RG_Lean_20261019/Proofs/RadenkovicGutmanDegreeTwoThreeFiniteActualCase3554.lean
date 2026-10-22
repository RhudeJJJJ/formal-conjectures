/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3554 : Family 8 := level8.get ⟨67,by decide⟩
def sourceMap3554 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3554 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3554_checked : acceptsGraphIso
    (source (graph core3554) (root 8) 0 6) DegreeTwoThreeSpectrum5623.graph sourceMap3554=true := by decide +kernel
theorem fusedMap3554_checked : acceptsGraphIso
    (fused (graph core3554) (root 8) 0 6) DegreeTwoThreeSpectrum5030.graph fusedMap3554=true := by decide +kernel
theorem certified3554 : Certified (graph core3554) (root 8) 0 6 :=
  of_native_maps core3554 DegreeTwoThreeSpectrum5623.graph DegreeTwoThreeSpectrum5030.graph
    sourceMap3554 fusedMap3554 sourceMap3554_checked fusedMap3554_checked
    DegreeTwoThreeFiniteComparisons.comparison3554
#print axioms sourceMap3554_checked
#print axioms fusedMap3554_checked
#print axioms certified3554
def sourceMap3554swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3554swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3554swap_checked : acceptsGraphIso
    (source (graph core3554) (root 8) 6 0) DegreeTwoThreeSpectrum5623.graph sourceMap3554swap=true := by decide +kernel
theorem fusedMap3554swap_checked : acceptsGraphIso
    (fused (graph core3554) (root 8) 6 0) DegreeTwoThreeSpectrum5030.graph fusedMap3554swap=true := by decide +kernel
theorem certified3554swap : Certified (graph core3554) (root 8) 6 0 :=
  of_native_maps core3554 DegreeTwoThreeSpectrum5623.graph DegreeTwoThreeSpectrum5030.graph
    sourceMap3554swap fusedMap3554swap sourceMap3554swap_checked fusedMap3554swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3554
#print axioms sourceMap3554swap_checked
#print axioms fusedMap3554swap_checked
#print axioms certified3554swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
