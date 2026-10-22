/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3677 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap3677 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3677 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3677_checked : acceptsGraphIso
    (source (graph core3677) (root 7) 0 7) DegreeTwoThreeSpectrum5743.graph sourceMap3677=true := by decide +kernel
theorem fusedMap3677_checked : acceptsGraphIso
    (fused (graph core3677) (root 7) 0 7) DegreeTwoThreeSpectrum5056.graph fusedMap3677=true := by decide +kernel
theorem certified3677 : Certified (graph core3677) (root 7) 0 7 :=
  of_native_maps core3677 DegreeTwoThreeSpectrum5743.graph DegreeTwoThreeSpectrum5056.graph
    sourceMap3677 fusedMap3677 sourceMap3677_checked fusedMap3677_checked
    DegreeTwoThreeFiniteComparisons.comparison3677
#print axioms sourceMap3677_checked
#print axioms fusedMap3677_checked
#print axioms certified3677
def sourceMap3677swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3677swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3677swap_checked : acceptsGraphIso
    (source (graph core3677) (root 7) 7 0) DegreeTwoThreeSpectrum5743.graph sourceMap3677swap=true := by decide +kernel
theorem fusedMap3677swap_checked : acceptsGraphIso
    (fused (graph core3677) (root 7) 7 0) DegreeTwoThreeSpectrum5056.graph fusedMap3677swap=true := by decide +kernel
theorem certified3677swap : Certified (graph core3677) (root 7) 7 0 :=
  of_native_maps core3677 DegreeTwoThreeSpectrum5743.graph DegreeTwoThreeSpectrum5056.graph
    sourceMap3677swap fusedMap3677swap sourceMap3677swap_checked fusedMap3677swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3677
#print axioms sourceMap3677swap_checked
#print axioms fusedMap3677swap_checked
#print axioms certified3677swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
