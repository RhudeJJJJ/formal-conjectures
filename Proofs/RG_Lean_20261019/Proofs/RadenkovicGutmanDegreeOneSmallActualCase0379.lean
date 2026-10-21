/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0379 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0379 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0379 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0379_checked : acceptsGraphIso
    (source (graph core0379) (root 6) 0 4) DegreeOneSmallSpectrum953.graph sourceMap0379=true := by decide +kernel
theorem fusedMap0379_checked : acceptsGraphIso
    (fused (graph core0379) (root 6) 0 4) DegreeOneSmallSpectrum956.graph fusedMap0379=true := by decide +kernel
theorem certified0379 : Certified (graph core0379) (root 6) 0 4 :=
  of_native_maps core0379 DegreeOneSmallSpectrum953.graph DegreeOneSmallSpectrum956.graph
    sourceMap0379 fusedMap0379 sourceMap0379_checked fusedMap0379_checked
    DegreeOneSmallComparisons.comparison0379
#print axioms sourceMap0379_checked
#print axioms fusedMap0379_checked
#print axioms certified0379
def sourceMap0379swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap0379swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0379swap_checked : acceptsGraphIso
    (source (graph core0379) (root 6) 4 0) DegreeOneSmallSpectrum953.graph sourceMap0379swap=true := by decide +kernel
theorem fusedMap0379swap_checked : acceptsGraphIso
    (fused (graph core0379) (root 6) 4 0) DegreeOneSmallSpectrum956.graph fusedMap0379swap=true := by decide +kernel
theorem certified0379swap : Certified (graph core0379) (root 6) 4 0 :=
  of_native_maps core0379 DegreeOneSmallSpectrum953.graph DegreeOneSmallSpectrum956.graph
    sourceMap0379swap fusedMap0379swap sourceMap0379swap_checked fusedMap0379swap_checked
    DegreeOneSmallComparisons.comparison0379
#print axioms sourceMap0379swap_checked
#print axioms fusedMap0379swap_checked
#print axioms certified0379swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
