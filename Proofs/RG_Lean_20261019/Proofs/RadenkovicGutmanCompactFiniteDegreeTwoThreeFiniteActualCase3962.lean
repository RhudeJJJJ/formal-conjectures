/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3962 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap3962 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3962 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3962_checked : acceptsGraphIso
    (source (graph core3962) (root 7) 1 5) DegreeTwoThreeSpectrum4512.graph sourceMap3962=true := by decide +kernel
theorem fusedMap3962_checked : acceptsGraphIso
    (fused (graph core3962) (root 7) 1 5) DegreeTwoThreeSpectrum4030.graph fusedMap3962=true := by decide +kernel
theorem certified3962 : Certified (graph core3962) (root 7) 1 5 :=
  of_native_maps core3962 DegreeTwoThreeSpectrum4512.graph DegreeTwoThreeSpectrum4030.graph
    sourceMap3962 fusedMap3962 sourceMap3962_checked fusedMap3962_checked
    DegreeTwoThreeFiniteComparisons.comparison3962
#print axioms sourceMap3962_checked
#print axioms fusedMap3962_checked
#print axioms certified3962
def sourceMap3962swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3962swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3962swap_checked : acceptsGraphIso
    (source (graph core3962) (root 7) 5 1) DegreeTwoThreeSpectrum4512.graph sourceMap3962swap=true := by decide +kernel
theorem fusedMap3962swap_checked : acceptsGraphIso
    (fused (graph core3962) (root 7) 5 1) DegreeTwoThreeSpectrum4030.graph fusedMap3962swap=true := by decide +kernel
theorem certified3962swap : Certified (graph core3962) (root 7) 5 1 :=
  of_native_maps core3962 DegreeTwoThreeSpectrum4512.graph DegreeTwoThreeSpectrum4030.graph
    sourceMap3962swap fusedMap3962swap sourceMap3962swap_checked fusedMap3962swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3962
#print axioms sourceMap3962swap_checked
#print axioms fusedMap3962swap_checked
#print axioms certified3962swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
