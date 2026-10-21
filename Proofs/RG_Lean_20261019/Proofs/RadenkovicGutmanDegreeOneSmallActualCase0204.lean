/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0204 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0204 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap0204 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap0204_checked : acceptsGraphIso
    (source (graph core0204) (root 5) 1 4) DegreeOneSmallSpectrum957.graph sourceMap0204=true := by decide +kernel
theorem fusedMap0204_checked : acceptsGraphIso
    (fused (graph core0204) (root 5) 1 4) DegreeOneSmallSpectrum858.graph fusedMap0204=true := by decide +kernel
theorem certified0204 : Certified (graph core0204) (root 5) 1 4 :=
  of_native_maps core0204 DegreeOneSmallSpectrum957.graph DegreeOneSmallSpectrum858.graph
    sourceMap0204 fusedMap0204 sourceMap0204_checked fusedMap0204_checked
    DegreeOneSmallComparisons.comparison0204
#print axioms sourceMap0204_checked
#print axioms fusedMap0204_checked
#print axioms certified0204
def sourceMap0204swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,12,6,7] (sourceLabel 5 4 1 v)
def fusedMap0204swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap0204swap_checked : acceptsGraphIso
    (source (graph core0204) (root 5) 4 1) DegreeOneSmallSpectrum957.graph sourceMap0204swap=true := by decide +kernel
theorem fusedMap0204swap_checked : acceptsGraphIso
    (fused (graph core0204) (root 5) 4 1) DegreeOneSmallSpectrum858.graph fusedMap0204swap=true := by decide +kernel
theorem certified0204swap : Certified (graph core0204) (root 5) 4 1 :=
  of_native_maps core0204 DegreeOneSmallSpectrum957.graph DegreeOneSmallSpectrum858.graph
    sourceMap0204swap fusedMap0204swap sourceMap0204swap_checked fusedMap0204swap_checked
    DegreeOneSmallComparisons.comparison0204
#print axioms sourceMap0204swap_checked
#print axioms fusedMap0204swap_checked
#print axioms certified0204swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
