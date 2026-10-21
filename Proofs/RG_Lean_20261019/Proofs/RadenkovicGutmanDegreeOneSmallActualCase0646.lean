/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0646 : Family 7 := level7.get ⟨50,by decide⟩
def sourceMap0646 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0646 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0646_checked : acceptsGraphIso
    (source (graph core0646) (root 7) 0 1) DegreeOneSmallSpectrum341.graph sourceMap0646=true := by decide +kernel
theorem fusedMap0646_checked : acceptsGraphIso
    (fused (graph core0646) (root 7) 0 1) DegreeOneSmallSpectrum218.graph fusedMap0646=true := by decide +kernel
theorem certified0646 : Certified (graph core0646) (root 7) 0 1 :=
  of_native_maps core0646 DegreeOneSmallSpectrum341.graph DegreeOneSmallSpectrum218.graph
    sourceMap0646 fusedMap0646 sourceMap0646_checked fusedMap0646_checked
    DegreeOneSmallComparisons.comparison0646
#print axioms sourceMap0646_checked
#print axioms fusedMap0646_checked
#print axioms certified0646
def sourceMap0646swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0646swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0646swap_checked : acceptsGraphIso
    (source (graph core0646) (root 7) 1 0) DegreeOneSmallSpectrum341.graph sourceMap0646swap=true := by decide +kernel
theorem fusedMap0646swap_checked : acceptsGraphIso
    (fused (graph core0646) (root 7) 1 0) DegreeOneSmallSpectrum218.graph fusedMap0646swap=true := by decide +kernel
theorem certified0646swap : Certified (graph core0646) (root 7) 1 0 :=
  of_native_maps core0646 DegreeOneSmallSpectrum341.graph DegreeOneSmallSpectrum218.graph
    sourceMap0646swap fusedMap0646swap sourceMap0646swap_checked fusedMap0646swap_checked
    DegreeOneSmallComparisons.comparison0646
#print axioms sourceMap0646swap_checked
#print axioms fusedMap0646swap_checked
#print axioms certified0646swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
