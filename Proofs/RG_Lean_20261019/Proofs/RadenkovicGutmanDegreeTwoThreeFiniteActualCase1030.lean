/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1030 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap1030 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,7,8,5,6] (sourceLabel 5 0 1 v)
def fusedMap1030 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap1030_checked : acceptsGraphIso
    (source (graph core1030) (root 5) 0 1) DegreeTwoThreeSpectrum064.graph sourceMap1030=true := by decide +kernel
theorem fusedMap1030_checked : acceptsGraphIso
    (fused (graph core1030) (root 5) 0 1) DegreeOneSmallSpectrum039.graph fusedMap1030=true := by decide +kernel
theorem certified1030 : Certified (graph core1030) (root 5) 0 1 :=
  of_native_maps core1030 DegreeTwoThreeSpectrum064.graph DegreeOneSmallSpectrum039.graph
    sourceMap1030 fusedMap1030 sourceMap1030_checked fusedMap1030_checked
    DegreeTwoThreeFiniteComparisons.comparison1030
#print axioms sourceMap1030_checked
#print axioms fusedMap1030_checked
#print axioms certified1030
def sourceMap1030swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,7,5,6,8] (sourceLabel 5 1 0 v)
def fusedMap1030swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap1030swap_checked : acceptsGraphIso
    (source (graph core1030) (root 5) 1 0) DegreeTwoThreeSpectrum064.graph sourceMap1030swap=true := by decide +kernel
theorem fusedMap1030swap_checked : acceptsGraphIso
    (fused (graph core1030) (root 5) 1 0) DegreeOneSmallSpectrum039.graph fusedMap1030swap=true := by decide +kernel
theorem certified1030swap : Certified (graph core1030) (root 5) 1 0 :=
  of_native_maps core1030 DegreeTwoThreeSpectrum064.graph DegreeOneSmallSpectrum039.graph
    sourceMap1030swap fusedMap1030swap sourceMap1030swap_checked fusedMap1030swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1030
#print axioms sourceMap1030swap_checked
#print axioms fusedMap1030swap_checked
#print axioms certified1030swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
