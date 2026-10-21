/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0610 : Family 7 := level7.get ⟨39,by decide⟩
def sourceMap0610 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0610 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0610_checked : acceptsGraphIso
    (source (graph core0610) (root 7) 0 1) DegreeOneSmallSpectrum323.graph sourceMap0610=true := by decide +kernel
theorem fusedMap0610_checked : acceptsGraphIso
    (fused (graph core0610) (root 7) 0 1) DegreeOneSmallSpectrum198.graph fusedMap0610=true := by decide +kernel
theorem certified0610 : Certified (graph core0610) (root 7) 0 1 :=
  of_native_maps core0610 DegreeOneSmallSpectrum323.graph DegreeOneSmallSpectrum198.graph
    sourceMap0610 fusedMap0610 sourceMap0610_checked fusedMap0610_checked
    DegreeOneSmallComparisons.comparison0610
#print axioms sourceMap0610_checked
#print axioms fusedMap0610_checked
#print axioms certified0610
def sourceMap0610swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0610swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0610swap_checked : acceptsGraphIso
    (source (graph core0610) (root 7) 1 0) DegreeOneSmallSpectrum323.graph sourceMap0610swap=true := by decide +kernel
theorem fusedMap0610swap_checked : acceptsGraphIso
    (fused (graph core0610) (root 7) 1 0) DegreeOneSmallSpectrum198.graph fusedMap0610swap=true := by decide +kernel
theorem certified0610swap : Certified (graph core0610) (root 7) 1 0 :=
  of_native_maps core0610 DegreeOneSmallSpectrum323.graph DegreeOneSmallSpectrum198.graph
    sourceMap0610swap fusedMap0610swap sourceMap0610swap_checked fusedMap0610swap_checked
    DegreeOneSmallComparisons.comparison0610
#print axioms sourceMap0610swap_checked
#print axioms fusedMap0610swap_checked
#print axioms certified0610swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
