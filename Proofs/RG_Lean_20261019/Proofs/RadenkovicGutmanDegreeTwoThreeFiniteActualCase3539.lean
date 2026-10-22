/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3539 : Family 8 := level8.get ⟨7,by decide⟩
def sourceMap3539 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,15,16,8,9,10,11,12,13,14] (sourceLabel 8 0 6 v)
def fusedMap3539 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3539_checked : acceptsGraphIso
    (source (graph core3539) (root 8) 0 6) DegreeTwoThreeSpectrum5134.graph sourceMap3539=true := by decide +kernel
theorem fusedMap3539_checked : acceptsGraphIso
    (fused (graph core3539) (root 8) 0 6) DegreeTwoThreeSpectrum4965.graph fusedMap3539=true := by decide +kernel
theorem certified3539 : Certified (graph core3539) (root 8) 0 6 :=
  of_native_maps core3539 DegreeTwoThreeSpectrum5134.graph DegreeTwoThreeSpectrum4965.graph
    sourceMap3539 fusedMap3539 sourceMap3539_checked fusedMap3539_checked
    DegreeTwoThreeFiniteComparisons.comparison3539
#print axioms sourceMap3539_checked
#print axioms fusedMap3539_checked
#print axioms certified3539
def sourceMap3539swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14,16] (sourceLabel 8 6 0 v)
def fusedMap3539swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3539swap_checked : acceptsGraphIso
    (source (graph core3539) (root 8) 6 0) DegreeTwoThreeSpectrum5134.graph sourceMap3539swap=true := by decide +kernel
theorem fusedMap3539swap_checked : acceptsGraphIso
    (fused (graph core3539) (root 8) 6 0) DegreeTwoThreeSpectrum4965.graph fusedMap3539swap=true := by decide +kernel
theorem certified3539swap : Certified (graph core3539) (root 8) 6 0 :=
  of_native_maps core3539 DegreeTwoThreeSpectrum5134.graph DegreeTwoThreeSpectrum4965.graph
    sourceMap3539swap fusedMap3539swap sourceMap3539swap_checked fusedMap3539swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3539
#print axioms sourceMap3539swap_checked
#print axioms fusedMap3539swap_checked
#print axioms certified3539swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
