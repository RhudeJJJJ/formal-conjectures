/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1053 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap1053 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7] (sourceLabel 6 0 2 v)
def fusedMap1053 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1053_checked : acceptsGraphIso
    (source (graph core1053) (root 6) 0 2) DegreeOneSmallSpectrum343.graph sourceMap1053=true := by decide +kernel
theorem fusedMap1053_checked : acceptsGraphIso
    (fused (graph core1053) (root 6) 0 2) DegreeOneSmallSpectrum208.graph fusedMap1053=true := by decide +kernel
theorem certified1053 : Certified (graph core1053) (root 6) 0 2 :=
  of_native_maps core1053 DegreeOneSmallSpectrum343.graph DegreeOneSmallSpectrum208.graph
    sourceMap1053 fusedMap1053 sourceMap1053_checked fusedMap1053_checked
    DegreeTwoThreeFiniteComparisons.comparison1053
#print axioms sourceMap1053_checked
#print axioms fusedMap1053_checked
#print axioms certified1053
def sourceMap1053swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,5,6,7,10] (sourceLabel 6 2 0 v)
def fusedMap1053swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1053swap_checked : acceptsGraphIso
    (source (graph core1053) (root 6) 2 0) DegreeOneSmallSpectrum343.graph sourceMap1053swap=true := by decide +kernel
theorem fusedMap1053swap_checked : acceptsGraphIso
    (fused (graph core1053) (root 6) 2 0) DegreeOneSmallSpectrum208.graph fusedMap1053swap=true := by decide +kernel
theorem certified1053swap : Certified (graph core1053) (root 6) 2 0 :=
  of_native_maps core1053 DegreeOneSmallSpectrum343.graph DegreeOneSmallSpectrum208.graph
    sourceMap1053swap fusedMap1053swap sourceMap1053swap_checked fusedMap1053swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1053
#print axioms sourceMap1053swap_checked
#print axioms fusedMap1053swap_checked
#print axioms certified1053swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
