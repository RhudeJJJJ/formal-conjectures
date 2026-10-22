/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3671 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap3671 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3671 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3671_checked : acceptsGraphIso
    (source (graph core3671) (root 7) 0 7) DegreeTwoThreeSpectrum5373.graph sourceMap3671=true := by decide +kernel
theorem fusedMap3671_checked : acceptsGraphIso
    (fused (graph core3671) (root 7) 0 7) DegreeTwoThreeSpectrum4988.graph fusedMap3671=true := by decide +kernel
theorem certified3671 : Certified (graph core3671) (root 7) 0 7 :=
  of_native_maps core3671 DegreeTwoThreeSpectrum5373.graph DegreeTwoThreeSpectrum4988.graph
    sourceMap3671 fusedMap3671 sourceMap3671_checked fusedMap3671_checked
    DegreeTwoThreeFiniteComparisons.comparison3671
#print axioms sourceMap3671_checked
#print axioms fusedMap3671_checked
#print axioms certified3671
def sourceMap3671swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3671swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3671swap_checked : acceptsGraphIso
    (source (graph core3671) (root 7) 7 0) DegreeTwoThreeSpectrum5373.graph sourceMap3671swap=true := by decide +kernel
theorem fusedMap3671swap_checked : acceptsGraphIso
    (fused (graph core3671) (root 7) 7 0) DegreeTwoThreeSpectrum4988.graph fusedMap3671swap=true := by decide +kernel
theorem certified3671swap : Certified (graph core3671) (root 7) 7 0 :=
  of_native_maps core3671 DegreeTwoThreeSpectrum5373.graph DegreeTwoThreeSpectrum4988.graph
    sourceMap3671swap fusedMap3671swap sourceMap3671swap_checked fusedMap3671swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3671
#print axioms sourceMap3671swap_checked
#print axioms fusedMap3671swap_checked
#print axioms certified3671swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
