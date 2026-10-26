/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3675 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap3675 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3675 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3675_checked : acceptsGraphIso
    (source (graph core3675) (root 7) 0 7) DegreeTwoThreeSpectrum5607.graph sourceMap3675=true := by decide +kernel
theorem fusedMap3675_checked : acceptsGraphIso
    (fused (graph core3675) (root 7) 0 7) DegreeTwoThreeSpectrum5028.graph fusedMap3675=true := by decide +kernel
theorem certified3675 : Certified (graph core3675) (root 7) 0 7 :=
  of_native_maps core3675 DegreeTwoThreeSpectrum5607.graph DegreeTwoThreeSpectrum5028.graph
    sourceMap3675 fusedMap3675 sourceMap3675_checked fusedMap3675_checked
    DegreeTwoThreeFiniteComparisons.comparison3675
#print axioms sourceMap3675_checked
#print axioms fusedMap3675_checked
#print axioms certified3675
def sourceMap3675swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3675swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3675swap_checked : acceptsGraphIso
    (source (graph core3675) (root 7) 7 0) DegreeTwoThreeSpectrum5607.graph sourceMap3675swap=true := by decide +kernel
theorem fusedMap3675swap_checked : acceptsGraphIso
    (fused (graph core3675) (root 7) 7 0) DegreeTwoThreeSpectrum5028.graph fusedMap3675swap=true := by decide +kernel
theorem certified3675swap : Certified (graph core3675) (root 7) 7 0 :=
  of_native_maps core3675 DegreeTwoThreeSpectrum5607.graph DegreeTwoThreeSpectrum5028.graph
    sourceMap3675swap fusedMap3675swap sourceMap3675swap_checked fusedMap3675swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3675
#print axioms sourceMap3675swap_checked
#print axioms fusedMap3675swap_checked
#print axioms certified3675swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
