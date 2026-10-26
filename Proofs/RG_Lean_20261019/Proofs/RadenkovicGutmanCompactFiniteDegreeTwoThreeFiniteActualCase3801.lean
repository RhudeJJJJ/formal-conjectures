/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3801 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap3801 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3801 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3801_checked : acceptsGraphIso
    (source (graph core3801) (root 7) 1 4) DegreeTwoThreeSpectrum2715.graph sourceMap3801=true := by decide +kernel
theorem fusedMap3801_checked : acceptsGraphIso
    (fused (graph core3801) (root 7) 1 4) DegreeTwoThreeSpectrum2356.graph fusedMap3801=true := by decide +kernel
theorem certified3801 : Certified (graph core3801) (root 7) 1 4 :=
  of_native_maps core3801 DegreeTwoThreeSpectrum2715.graph DegreeTwoThreeSpectrum2356.graph
    sourceMap3801 fusedMap3801 sourceMap3801_checked fusedMap3801_checked
    DegreeTwoThreeFiniteComparisons.comparison3801
#print axioms sourceMap3801_checked
#print axioms fusedMap3801_checked
#print axioms certified3801
def sourceMap3801swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,7,8] (sourceLabel 7 4 1 v)
def fusedMap3801swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3801swap_checked : acceptsGraphIso
    (source (graph core3801) (root 7) 4 1) DegreeTwoThreeSpectrum2715.graph sourceMap3801swap=true := by decide +kernel
theorem fusedMap3801swap_checked : acceptsGraphIso
    (fused (graph core3801) (root 7) 4 1) DegreeTwoThreeSpectrum2356.graph fusedMap3801swap=true := by decide +kernel
theorem certified3801swap : Certified (graph core3801) (root 7) 4 1 :=
  of_native_maps core3801 DegreeTwoThreeSpectrum2715.graph DegreeTwoThreeSpectrum2356.graph
    sourceMap3801swap fusedMap3801swap sourceMap3801swap_checked fusedMap3801swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3801
#print axioms sourceMap3801swap_checked
#print axioms fusedMap3801swap_checked
#print axioms certified3801swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
