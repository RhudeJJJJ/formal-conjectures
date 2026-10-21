/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0909 : Family 8 := level8.get ⟨58,by decide⟩
def sourceMap0909 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0909 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0909_checked : acceptsGraphIso
    (source (graph core0909) (root 8) 0 2) DegreeOneSmallSpectrum1379.graph sourceMap0909=true := by decide +kernel
theorem fusedMap0909_checked : acceptsGraphIso
    (fused (graph core0909) (root 8) 0 2) DegreeOneSmallSpectrum917.graph fusedMap0909=true := by decide +kernel
theorem certified0909 : Certified (graph core0909) (root 8) 0 2 :=
  of_native_maps core0909 DegreeOneSmallSpectrum1379.graph DegreeOneSmallSpectrum917.graph
    sourceMap0909 fusedMap0909 sourceMap0909_checked fusedMap0909_checked
    DegreeOneSmallComparisons.comparison0909
#print axioms sourceMap0909_checked
#print axioms fusedMap0909_checked
#print axioms certified0909
def sourceMap0909swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0909swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0909swap_checked : acceptsGraphIso
    (source (graph core0909) (root 8) 2 0) DegreeOneSmallSpectrum1379.graph sourceMap0909swap=true := by decide +kernel
theorem fusedMap0909swap_checked : acceptsGraphIso
    (fused (graph core0909) (root 8) 2 0) DegreeOneSmallSpectrum917.graph fusedMap0909swap=true := by decide +kernel
theorem certified0909swap : Certified (graph core0909) (root 8) 2 0 :=
  of_native_maps core0909 DegreeOneSmallSpectrum1379.graph DegreeOneSmallSpectrum917.graph
    sourceMap0909swap fusedMap0909swap sourceMap0909swap_checked fusedMap0909swap_checked
    DegreeOneSmallComparisons.comparison0909
#print axioms sourceMap0909swap_checked
#print axioms fusedMap0909swap_checked
#print axioms certified0909swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
