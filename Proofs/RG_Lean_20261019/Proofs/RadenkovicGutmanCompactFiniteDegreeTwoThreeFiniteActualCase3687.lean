/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3687 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap3687 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3687 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3687_checked : acceptsGraphIso
    (source (graph core3687) (root 7) 0 7) DegreeTwoThreeSpectrum5307.graph sourceMap3687=true := by decide +kernel
theorem fusedMap3687_checked : acceptsGraphIso
    (fused (graph core3687) (root 7) 0 7) DegreeTwoThreeSpectrum5310.graph fusedMap3687=true := by decide +kernel
theorem certified3687 : Certified (graph core3687) (root 7) 0 7 :=
  of_native_maps core3687 DegreeTwoThreeSpectrum5307.graph DegreeTwoThreeSpectrum5310.graph
    sourceMap3687 fusedMap3687 sourceMap3687_checked fusedMap3687_checked
    DegreeTwoThreeFiniteComparisons.comparison3687
#print axioms sourceMap3687_checked
#print axioms fusedMap3687_checked
#print axioms certified3687
def sourceMap3687swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3687swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3687swap_checked : acceptsGraphIso
    (source (graph core3687) (root 7) 7 0) DegreeTwoThreeSpectrum5307.graph sourceMap3687swap=true := by decide +kernel
theorem fusedMap3687swap_checked : acceptsGraphIso
    (fused (graph core3687) (root 7) 7 0) DegreeTwoThreeSpectrum5310.graph fusedMap3687swap=true := by decide +kernel
theorem certified3687swap : Certified (graph core3687) (root 7) 7 0 :=
  of_native_maps core3687 DegreeTwoThreeSpectrum5307.graph DegreeTwoThreeSpectrum5310.graph
    sourceMap3687swap fusedMap3687swap sourceMap3687swap_checked fusedMap3687swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3687
#print axioms sourceMap3687swap_checked
#print axioms fusedMap3687swap_checked
#print axioms certified3687swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
