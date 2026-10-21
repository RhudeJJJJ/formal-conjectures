/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0544 : Family 7 := level7.get ⟨19,by decide⟩
def sourceMap0544 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0544 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (fusedLabel 7 0 1 v)
theorem sourceMap0544_checked : acceptsGraphIso
    (source (graph core0544) (root 7) 0 1) DegreeOneSmallSpectrum211.graph sourceMap0544=true := by decide +kernel
theorem fusedMap0544_checked : acceptsGraphIso
    (fused (graph core0544) (root 7) 0 1) DegreeOneSmallSpectrum227.graph fusedMap0544=true := by decide +kernel
theorem certified0544 : Certified (graph core0544) (root 7) 0 1 :=
  of_native_maps core0544 DegreeOneSmallSpectrum211.graph DegreeOneSmallSpectrum227.graph
    sourceMap0544 fusedMap0544 sourceMap0544_checked fusedMap0544_checked
    DegreeOneSmallComparisons.comparison0544
#print axioms sourceMap0544_checked
#print axioms fusedMap0544_checked
#print axioms certified0544
def sourceMap0544swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0544swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (fusedLabel 7 1 0 v)
theorem sourceMap0544swap_checked : acceptsGraphIso
    (source (graph core0544) (root 7) 1 0) DegreeOneSmallSpectrum211.graph sourceMap0544swap=true := by decide +kernel
theorem fusedMap0544swap_checked : acceptsGraphIso
    (fused (graph core0544) (root 7) 1 0) DegreeOneSmallSpectrum227.graph fusedMap0544swap=true := by decide +kernel
theorem certified0544swap : Certified (graph core0544) (root 7) 1 0 :=
  of_native_maps core0544 DegreeOneSmallSpectrum211.graph DegreeOneSmallSpectrum227.graph
    sourceMap0544swap fusedMap0544swap sourceMap0544swap_checked fusedMap0544swap_checked
    DegreeOneSmallComparisons.comparison0544
#print axioms sourceMap0544swap_checked
#print axioms fusedMap0544swap_checked
#print axioms certified0544swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
