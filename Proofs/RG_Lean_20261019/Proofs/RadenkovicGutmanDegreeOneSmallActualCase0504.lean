/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0504 : Family 7 := level7.get ⟨10,by decide⟩
def sourceMap0504 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0504 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0504_checked : acceptsGraphIso
    (source (graph core0504) (root 7) 0 3) DegreeOneSmallSpectrum893.graph sourceMap0504=true := by decide +kernel
theorem fusedMap0504_checked : acceptsGraphIso
    (fused (graph core0504) (root 7) 0 3) DegreeOneSmallSpectrum894.graph fusedMap0504=true := by decide +kernel
theorem certified0504 : Certified (graph core0504) (root 7) 0 3 :=
  of_native_maps core0504 DegreeOneSmallSpectrum893.graph DegreeOneSmallSpectrum894.graph
    sourceMap0504 fusedMap0504 sourceMap0504_checked fusedMap0504_checked
    DegreeOneSmallComparisons.comparison0504
#print axioms sourceMap0504_checked
#print axioms fusedMap0504_checked
#print axioms certified0504
def sourceMap0504swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0504swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0504swap_checked : acceptsGraphIso
    (source (graph core0504) (root 7) 3 0) DegreeOneSmallSpectrum893.graph sourceMap0504swap=true := by decide +kernel
theorem fusedMap0504swap_checked : acceptsGraphIso
    (fused (graph core0504) (root 7) 3 0) DegreeOneSmallSpectrum894.graph fusedMap0504swap=true := by decide +kernel
theorem certified0504swap : Certified (graph core0504) (root 7) 3 0 :=
  of_native_maps core0504 DegreeOneSmallSpectrum893.graph DegreeOneSmallSpectrum894.graph
    sourceMap0504swap fusedMap0504swap sourceMap0504swap_checked fusedMap0504swap_checked
    DegreeOneSmallComparisons.comparison0504
#print axioms sourceMap0504swap_checked
#print axioms fusedMap0504swap_checked
#print axioms certified0504swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
