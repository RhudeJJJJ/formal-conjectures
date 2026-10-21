/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0154 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0154 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (sourceLabel 4 1 5 v)
def fusedMap0154 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 1 5 v)
theorem sourceMap0154_checked : acceptsGraphIso
    (source (graph core0154) (root 4) 1 5) DegreeOneSmallSpectrum1015.graph sourceMap0154=true := by decide +kernel
theorem fusedMap0154_checked : acceptsGraphIso
    (fused (graph core0154) (root 4) 1 5) DegreeOneSmallSpectrum870.graph fusedMap0154=true := by decide +kernel
theorem certified0154 : Certified (graph core0154) (root 4) 1 5 :=
  of_native_maps core0154 DegreeOneSmallSpectrum1015.graph DegreeOneSmallSpectrum870.graph
    sourceMap0154 fusedMap0154 sourceMap0154_checked fusedMap0154_checked
    DegreeOneSmallComparisons.comparison0154
#print axioms sourceMap0154_checked
#print axioms fusedMap0154_checked
#print axioms certified0154
def sourceMap0154swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,9,10,11,12,7,8] (sourceLabel 4 5 1 v)
def fusedMap0154swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 5 1 v)
theorem sourceMap0154swap_checked : acceptsGraphIso
    (source (graph core0154) (root 4) 5 1) DegreeOneSmallSpectrum1015.graph sourceMap0154swap=true := by decide +kernel
theorem fusedMap0154swap_checked : acceptsGraphIso
    (fused (graph core0154) (root 4) 5 1) DegreeOneSmallSpectrum870.graph fusedMap0154swap=true := by decide +kernel
theorem certified0154swap : Certified (graph core0154) (root 4) 5 1 :=
  of_native_maps core0154 DegreeOneSmallSpectrum1015.graph DegreeOneSmallSpectrum870.graph
    sourceMap0154swap fusedMap0154swap sourceMap0154swap_checked fusedMap0154swap_checked
    DegreeOneSmallComparisons.comparison0154
#print axioms sourceMap0154swap_checked
#print axioms fusedMap0154swap_checked
#print axioms certified0154swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
