/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3686 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap3686 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3686 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3686_checked : acceptsGraphIso
    (source (graph core3686) (root 7) 0 7) DegreeTwoThreeSpectrum5266.graph sourceMap3686=true := by decide +kernel
theorem fusedMap3686_checked : acceptsGraphIso
    (fused (graph core3686) (root 7) 0 7) DegreeTwoThreeSpectrum5269.graph fusedMap3686=true := by decide +kernel
theorem certified3686 : Certified (graph core3686) (root 7) 0 7 :=
  of_native_maps core3686 DegreeTwoThreeSpectrum5266.graph DegreeTwoThreeSpectrum5269.graph
    sourceMap3686 fusedMap3686 sourceMap3686_checked fusedMap3686_checked
    DegreeTwoThreeFiniteComparisons.comparison3686
#print axioms sourceMap3686_checked
#print axioms fusedMap3686_checked
#print axioms certified3686
def sourceMap3686swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3686swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3686swap_checked : acceptsGraphIso
    (source (graph core3686) (root 7) 7 0) DegreeTwoThreeSpectrum5266.graph sourceMap3686swap=true := by decide +kernel
theorem fusedMap3686swap_checked : acceptsGraphIso
    (fused (graph core3686) (root 7) 7 0) DegreeTwoThreeSpectrum5269.graph fusedMap3686swap=true := by decide +kernel
theorem certified3686swap : Certified (graph core3686) (root 7) 7 0 :=
  of_native_maps core3686 DegreeTwoThreeSpectrum5266.graph DegreeTwoThreeSpectrum5269.graph
    sourceMap3686swap fusedMap3686swap sourceMap3686swap_checked fusedMap3686swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3686
#print axioms sourceMap3686swap_checked
#print axioms fusedMap3686swap_checked
#print axioms certified3686swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
