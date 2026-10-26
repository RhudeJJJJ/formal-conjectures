/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3572 : Family 8 := level8.get ⟨118,by decide⟩
def sourceMap3572 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3572 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3572_checked : acceptsGraphIso
    (source (graph core3572) (root 8) 0 6) DegreeTwoThreeSpectrum5284.graph sourceMap3572=true := by decide +kernel
theorem fusedMap3572_checked : acceptsGraphIso
    (fused (graph core3572) (root 8) 0 6) DegreeTwoThreeSpectrum5286.graph fusedMap3572=true := by decide +kernel
theorem certified3572 : Certified (graph core3572) (root 8) 0 6 :=
  of_native_maps core3572 DegreeTwoThreeSpectrum5284.graph DegreeTwoThreeSpectrum5286.graph
    sourceMap3572 fusedMap3572 sourceMap3572_checked fusedMap3572_checked
    DegreeTwoThreeFiniteComparisons.comparison3572
#print axioms sourceMap3572_checked
#print axioms fusedMap3572_checked
#print axioms certified3572
def sourceMap3572swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3572swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3572swap_checked : acceptsGraphIso
    (source (graph core3572) (root 8) 6 0) DegreeTwoThreeSpectrum5284.graph sourceMap3572swap=true := by decide +kernel
theorem fusedMap3572swap_checked : acceptsGraphIso
    (fused (graph core3572) (root 8) 6 0) DegreeTwoThreeSpectrum5286.graph fusedMap3572swap=true := by decide +kernel
theorem certified3572swap : Certified (graph core3572) (root 8) 6 0 :=
  of_native_maps core3572 DegreeTwoThreeSpectrum5284.graph DegreeTwoThreeSpectrum5286.graph
    sourceMap3572swap fusedMap3572swap sourceMap3572swap_checked fusedMap3572swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3572
#print axioms sourceMap3572swap_checked
#print axioms fusedMap3572swap_checked
#print axioms certified3572swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
