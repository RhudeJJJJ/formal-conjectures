/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3672 : Family 7 := level7.get ⟨41,by decide⟩
def sourceMap3672 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3672 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3672_checked : acceptsGraphIso
    (source (graph core3672) (root 7) 0 7) DegreeTwoThreeSpectrum5465.graph sourceMap3672=true := by decide +kernel
theorem fusedMap3672_checked : acceptsGraphIso
    (fused (graph core3672) (root 7) 0 7) DegreeTwoThreeSpectrum5010.graph fusedMap3672=true := by decide +kernel
theorem certified3672 : Certified (graph core3672) (root 7) 0 7 :=
  of_native_maps core3672 DegreeTwoThreeSpectrum5465.graph DegreeTwoThreeSpectrum5010.graph
    sourceMap3672 fusedMap3672 sourceMap3672_checked fusedMap3672_checked
    DegreeTwoThreeFiniteComparisons.comparison3672
#print axioms sourceMap3672_checked
#print axioms fusedMap3672_checked
#print axioms certified3672
def sourceMap3672swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3672swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3672swap_checked : acceptsGraphIso
    (source (graph core3672) (root 7) 7 0) DegreeTwoThreeSpectrum5465.graph sourceMap3672swap=true := by decide +kernel
theorem fusedMap3672swap_checked : acceptsGraphIso
    (fused (graph core3672) (root 7) 7 0) DegreeTwoThreeSpectrum5010.graph fusedMap3672swap=true := by decide +kernel
theorem certified3672swap : Certified (graph core3672) (root 7) 7 0 :=
  of_native_maps core3672 DegreeTwoThreeSpectrum5465.graph DegreeTwoThreeSpectrum5010.graph
    sourceMap3672swap fusedMap3672swap sourceMap3672swap_checked fusedMap3672swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3672
#print axioms sourceMap3672swap_checked
#print axioms fusedMap3672swap_checked
#print axioms certified3672swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
