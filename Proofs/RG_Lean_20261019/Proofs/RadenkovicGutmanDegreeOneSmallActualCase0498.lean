/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0498 : Family 7 := level7.get ⟨9,by decide⟩
def sourceMap0498 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0498 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0498_checked : acceptsGraphIso
    (source (graph core0498) (root 7) 0 3) DegreeOneSmallSpectrum886.graph sourceMap0498=true := by decide +kernel
theorem fusedMap0498_checked : acceptsGraphIso
    (fused (graph core0498) (root 7) 0 3) DegreeOneSmallSpectrum887.graph fusedMap0498=true := by decide +kernel
theorem certified0498 : Certified (graph core0498) (root 7) 0 3 :=
  of_native_maps core0498 DegreeOneSmallSpectrum886.graph DegreeOneSmallSpectrum887.graph
    sourceMap0498 fusedMap0498 sourceMap0498_checked fusedMap0498_checked
    DegreeOneSmallComparisons.comparison0498
#print axioms sourceMap0498_checked
#print axioms fusedMap0498_checked
#print axioms certified0498
def sourceMap0498swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0498swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0498swap_checked : acceptsGraphIso
    (source (graph core0498) (root 7) 3 0) DegreeOneSmallSpectrum886.graph sourceMap0498swap=true := by decide +kernel
theorem fusedMap0498swap_checked : acceptsGraphIso
    (fused (graph core0498) (root 7) 3 0) DegreeOneSmallSpectrum887.graph fusedMap0498swap=true := by decide +kernel
theorem certified0498swap : Certified (graph core0498) (root 7) 3 0 :=
  of_native_maps core0498 DegreeOneSmallSpectrum886.graph DegreeOneSmallSpectrum887.graph
    sourceMap0498swap fusedMap0498swap sourceMap0498swap_checked fusedMap0498swap_checked
    DegreeOneSmallComparisons.comparison0498
#print axioms sourceMap0498swap_checked
#print axioms fusedMap0498swap_checked
#print axioms certified0498swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
