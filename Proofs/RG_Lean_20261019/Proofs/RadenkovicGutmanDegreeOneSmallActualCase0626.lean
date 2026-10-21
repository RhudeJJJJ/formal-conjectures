/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0626 : Family 7 := level7.get ⟨42,by decide⟩
def sourceMap0626 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0626 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0626_checked : acceptsGraphIso
    (source (graph core0626) (root 7) 1 2) DegreeOneSmallSpectrum1361.graph sourceMap0626=true := by decide +kernel
theorem fusedMap0626_checked : acceptsGraphIso
    (fused (graph core0626) (root 7) 1 2) DegreeOneSmallSpectrum916.graph fusedMap0626=true := by decide +kernel
theorem certified0626 : Certified (graph core0626) (root 7) 1 2 :=
  of_native_maps core0626 DegreeOneSmallSpectrum1361.graph DegreeOneSmallSpectrum916.graph
    sourceMap0626 fusedMap0626 sourceMap0626_checked fusedMap0626_checked
    DegreeOneSmallComparisons.comparison0626
#print axioms sourceMap0626_checked
#print axioms fusedMap0626_checked
#print axioms certified0626
def sourceMap0626swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0626swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0626swap_checked : acceptsGraphIso
    (source (graph core0626) (root 7) 2 1) DegreeOneSmallSpectrum1361.graph sourceMap0626swap=true := by decide +kernel
theorem fusedMap0626swap_checked : acceptsGraphIso
    (fused (graph core0626) (root 7) 2 1) DegreeOneSmallSpectrum916.graph fusedMap0626swap=true := by decide +kernel
theorem certified0626swap : Certified (graph core0626) (root 7) 2 1 :=
  of_native_maps core0626 DegreeOneSmallSpectrum1361.graph DegreeOneSmallSpectrum916.graph
    sourceMap0626swap fusedMap0626swap sourceMap0626swap_checked fusedMap0626swap_checked
    DegreeOneSmallComparisons.comparison0626
#print axioms sourceMap0626swap_checked
#print axioms fusedMap0626swap_checked
#print axioms certified0626swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
