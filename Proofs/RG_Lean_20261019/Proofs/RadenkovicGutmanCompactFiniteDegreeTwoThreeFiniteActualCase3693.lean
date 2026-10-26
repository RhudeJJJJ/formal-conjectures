/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3693 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap3693 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3693 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3693_checked : acceptsGraphIso
    (source (graph core3693) (root 7) 0 7) DegreeTwoThreeSpectrum5541.graph sourceMap3693=true := by decide +kernel
theorem fusedMap3693_checked : acceptsGraphIso
    (fused (graph core3693) (root 7) 0 7) DegreeTwoThreeSpectrum5544.graph fusedMap3693=true := by decide +kernel
theorem certified3693 : Certified (graph core3693) (root 7) 0 7 :=
  of_native_maps core3693 DegreeTwoThreeSpectrum5541.graph DegreeTwoThreeSpectrum5544.graph
    sourceMap3693 fusedMap3693 sourceMap3693_checked fusedMap3693_checked
    DegreeTwoThreeFiniteComparisons.comparison3693
#print axioms sourceMap3693_checked
#print axioms fusedMap3693_checked
#print axioms certified3693
def sourceMap3693swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3693swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3693swap_checked : acceptsGraphIso
    (source (graph core3693) (root 7) 7 0) DegreeTwoThreeSpectrum5541.graph sourceMap3693swap=true := by decide +kernel
theorem fusedMap3693swap_checked : acceptsGraphIso
    (fused (graph core3693) (root 7) 7 0) DegreeTwoThreeSpectrum5544.graph fusedMap3693swap=true := by decide +kernel
theorem certified3693swap : Certified (graph core3693) (root 7) 7 0 :=
  of_native_maps core3693 DegreeTwoThreeSpectrum5541.graph DegreeTwoThreeSpectrum5544.graph
    sourceMap3693swap fusedMap3693swap sourceMap3693swap_checked fusedMap3693swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3693
#print axioms sourceMap3693swap_checked
#print axioms fusedMap3693swap_checked
#print axioms certified3693swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
