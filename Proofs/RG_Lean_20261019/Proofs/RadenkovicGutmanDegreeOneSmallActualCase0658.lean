/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0658 : Family 7 := level7.get ⟨52,by decide⟩
def sourceMap0658 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0658 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0658_checked : acceptsGraphIso
    (source (graph core0658) (root 7) 0 1) DegreeOneSmallSpectrum343.graph sourceMap0658=true := by decide +kernel
theorem fusedMap0658_checked : acceptsGraphIso
    (fused (graph core0658) (root 7) 0 1) DegreeOneSmallSpectrum220.graph fusedMap0658=true := by decide +kernel
theorem certified0658 : Certified (graph core0658) (root 7) 0 1 :=
  of_native_maps core0658 DegreeOneSmallSpectrum343.graph DegreeOneSmallSpectrum220.graph
    sourceMap0658 fusedMap0658 sourceMap0658_checked fusedMap0658_checked
    DegreeOneSmallComparisons.comparison0658
#print axioms sourceMap0658_checked
#print axioms fusedMap0658_checked
#print axioms certified0658
def sourceMap0658swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0658swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0658swap_checked : acceptsGraphIso
    (source (graph core0658) (root 7) 1 0) DegreeOneSmallSpectrum343.graph sourceMap0658swap=true := by decide +kernel
theorem fusedMap0658swap_checked : acceptsGraphIso
    (fused (graph core0658) (root 7) 1 0) DegreeOneSmallSpectrum220.graph fusedMap0658swap=true := by decide +kernel
theorem certified0658swap : Certified (graph core0658) (root 7) 1 0 :=
  of_native_maps core0658 DegreeOneSmallSpectrum343.graph DegreeOneSmallSpectrum220.graph
    sourceMap0658swap fusedMap0658swap sourceMap0658swap_checked fusedMap0658swap_checked
    DegreeOneSmallComparisons.comparison0658
#print axioms sourceMap0658swap_checked
#print axioms fusedMap0658swap_checked
#print axioms certified0658swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
