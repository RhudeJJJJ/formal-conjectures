/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0756 : Family 8 := level8.get ⟨5,by decide⟩
def sourceMap0756 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0756 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (fusedLabel 8 0 1 v)
theorem sourceMap0756_checked : acceptsGraphIso
    (source (graph core0756) (root 8) 0 1) DegreeOneSmallSpectrum382.graph sourceMap0756=true := by decide +kernel
theorem fusedMap0756_checked : acceptsGraphIso
    (fused (graph core0756) (root 8) 0 1) DegreeOneSmallSpectrum397.graph fusedMap0756=true := by decide +kernel
theorem certified0756 : Certified (graph core0756) (root 8) 0 1 :=
  of_native_maps core0756 DegreeOneSmallSpectrum382.graph DegreeOneSmallSpectrum397.graph
    sourceMap0756 fusedMap0756 sourceMap0756_checked fusedMap0756_checked
    DegreeOneSmallComparisons.comparison0756
#print axioms sourceMap0756_checked
#print axioms fusedMap0756_checked
#print axioms certified0756
def sourceMap0756swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0756swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (fusedLabel 8 1 0 v)
theorem sourceMap0756swap_checked : acceptsGraphIso
    (source (graph core0756) (root 8) 1 0) DegreeOneSmallSpectrum382.graph sourceMap0756swap=true := by decide +kernel
theorem fusedMap0756swap_checked : acceptsGraphIso
    (fused (graph core0756) (root 8) 1 0) DegreeOneSmallSpectrum397.graph fusedMap0756swap=true := by decide +kernel
theorem certified0756swap : Certified (graph core0756) (root 8) 1 0 :=
  of_native_maps core0756 DegreeOneSmallSpectrum382.graph DegreeOneSmallSpectrum397.graph
    sourceMap0756swap fusedMap0756swap sourceMap0756swap_checked fusedMap0756swap_checked
    DegreeOneSmallComparisons.comparison0756
#print axioms sourceMap0756swap_checked
#print axioms fusedMap0756swap_checked
#print axioms certified0756swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
