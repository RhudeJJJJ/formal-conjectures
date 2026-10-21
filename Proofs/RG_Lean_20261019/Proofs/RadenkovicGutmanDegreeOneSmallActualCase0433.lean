/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0433 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0433 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0433 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0433_checked : acceptsGraphIso
    (source (graph core0433) (root 6) 0 4) DegreeOneSmallSpectrum1358.graph sourceMap0433=true := by decide +kernel
theorem fusedMap0433_checked : acceptsGraphIso
    (fused (graph core0433) (root 6) 0 4) DegreeOneSmallSpectrum916.graph fusedMap0433=true := by decide +kernel
theorem certified0433 : Certified (graph core0433) (root 6) 0 4 :=
  of_native_maps core0433 DegreeOneSmallSpectrum1358.graph DegreeOneSmallSpectrum916.graph
    sourceMap0433 fusedMap0433 sourceMap0433_checked fusedMap0433_checked
    DegreeOneSmallComparisons.comparison0433
#print axioms sourceMap0433_checked
#print axioms fusedMap0433_checked
#print axioms certified0433
def sourceMap0433swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap0433swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0433swap_checked : acceptsGraphIso
    (source (graph core0433) (root 6) 4 0) DegreeOneSmallSpectrum1358.graph sourceMap0433swap=true := by decide +kernel
theorem fusedMap0433swap_checked : acceptsGraphIso
    (fused (graph core0433) (root 6) 4 0) DegreeOneSmallSpectrum916.graph fusedMap0433swap=true := by decide +kernel
theorem certified0433swap : Certified (graph core0433) (root 6) 4 0 :=
  of_native_maps core0433 DegreeOneSmallSpectrum1358.graph DegreeOneSmallSpectrum916.graph
    sourceMap0433swap fusedMap0433swap sourceMap0433swap_checked fusedMap0433swap_checked
    DegreeOneSmallComparisons.comparison0433
#print axioms sourceMap0433swap_checked
#print axioms fusedMap0433swap_checked
#print axioms certified0433swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
