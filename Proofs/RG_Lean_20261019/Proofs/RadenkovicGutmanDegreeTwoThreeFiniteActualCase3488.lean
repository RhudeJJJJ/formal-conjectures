/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3488 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap3488 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3488 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3488_checked : acceptsGraphIso
    (source (graph core3488) (root 6) 0 6) DegreeTwoThreeSpectrum2367.graph sourceMap3488=true := by decide +kernel
theorem fusedMap3488_checked : acceptsGraphIso
    (fused (graph core3488) (root 6) 0 6) DegreeTwoThreeSpectrum2370.graph fusedMap3488=true := by decide +kernel
theorem certified3488 : Certified (graph core3488) (root 6) 0 6 :=
  of_native_maps core3488 DegreeTwoThreeSpectrum2367.graph DegreeTwoThreeSpectrum2370.graph
    sourceMap3488 fusedMap3488 sourceMap3488_checked fusedMap3488_checked
    DegreeTwoThreeFiniteComparisons.comparison3488
#print axioms sourceMap3488_checked
#print axioms fusedMap3488_checked
#print axioms certified3488
def sourceMap3488swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,14,8] (sourceLabel 6 6 0 v)
def fusedMap3488swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3488swap_checked : acceptsGraphIso
    (source (graph core3488) (root 6) 6 0) DegreeTwoThreeSpectrum2367.graph sourceMap3488swap=true := by decide +kernel
theorem fusedMap3488swap_checked : acceptsGraphIso
    (fused (graph core3488) (root 6) 6 0) DegreeTwoThreeSpectrum2370.graph fusedMap3488swap=true := by decide +kernel
theorem certified3488swap : Certified (graph core3488) (root 6) 6 0 :=
  of_native_maps core3488 DegreeTwoThreeSpectrum2367.graph DegreeTwoThreeSpectrum2370.graph
    sourceMap3488swap fusedMap3488swap sourceMap3488swap_checked fusedMap3488swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3488
#print axioms sourceMap3488swap_checked
#print axioms fusedMap3488swap_checked
#print axioms certified3488swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
