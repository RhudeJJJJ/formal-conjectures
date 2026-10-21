/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0538 : Family 7 := level7.get ⟨18,by decide⟩
def sourceMap0538 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0538 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0538_checked : acceptsGraphIso
    (source (graph core0538) (root 7) 0 1) DegreeOneSmallSpectrum215.graph sourceMap0538=true := by decide +kernel
theorem fusedMap0538_checked : acceptsGraphIso
    (fused (graph core0538) (root 7) 0 1) DegreeOneSmallSpectrum225.graph fusedMap0538=true := by decide +kernel
theorem certified0538 : Certified (graph core0538) (root 7) 0 1 :=
  of_native_maps core0538 DegreeOneSmallSpectrum215.graph DegreeOneSmallSpectrum225.graph
    sourceMap0538 fusedMap0538 sourceMap0538_checked fusedMap0538_checked
    DegreeOneSmallComparisons.comparison0538
#print axioms sourceMap0538_checked
#print axioms fusedMap0538_checked
#print axioms certified0538
def sourceMap0538swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0538swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0538swap_checked : acceptsGraphIso
    (source (graph core0538) (root 7) 1 0) DegreeOneSmallSpectrum215.graph sourceMap0538swap=true := by decide +kernel
theorem fusedMap0538swap_checked : acceptsGraphIso
    (fused (graph core0538) (root 7) 1 0) DegreeOneSmallSpectrum225.graph fusedMap0538swap=true := by decide +kernel
theorem certified0538swap : Certified (graph core0538) (root 7) 1 0 :=
  of_native_maps core0538 DegreeOneSmallSpectrum215.graph DegreeOneSmallSpectrum225.graph
    sourceMap0538swap fusedMap0538swap sourceMap0538swap_checked fusedMap0538swap_checked
    DegreeOneSmallComparisons.comparison0538
#print axioms sourceMap0538swap_checked
#print axioms fusedMap0538swap_checked
#print axioms certified0538swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
