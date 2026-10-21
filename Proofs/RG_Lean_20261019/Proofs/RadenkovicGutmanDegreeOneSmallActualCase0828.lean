/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0828 : Family 8 := level8.get ⟨27,by decide⟩
def sourceMap0828 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0828 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (fusedLabel 8 0 1 v)
theorem sourceMap0828_checked : acceptsGraphIso
    (source (graph core0828) (root 8) 0 1) DegreeOneSmallSpectrum550.graph sourceMap0828=true := by decide +kernel
theorem fusedMap0828_checked : acceptsGraphIso
    (fused (graph core0828) (root 8) 0 1) DegreeOneSmallSpectrum395.graph fusedMap0828=true := by decide +kernel
theorem certified0828 : Certified (graph core0828) (root 8) 0 1 :=
  of_native_maps core0828 DegreeOneSmallSpectrum550.graph DegreeOneSmallSpectrum395.graph
    sourceMap0828 fusedMap0828 sourceMap0828_checked fusedMap0828_checked
    DegreeOneSmallComparisons.comparison0828
#print axioms sourceMap0828_checked
#print axioms fusedMap0828_checked
#print axioms certified0828
def sourceMap0828swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0828swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (fusedLabel 8 1 0 v)
theorem sourceMap0828swap_checked : acceptsGraphIso
    (source (graph core0828) (root 8) 1 0) DegreeOneSmallSpectrum550.graph sourceMap0828swap=true := by decide +kernel
theorem fusedMap0828swap_checked : acceptsGraphIso
    (fused (graph core0828) (root 8) 1 0) DegreeOneSmallSpectrum395.graph fusedMap0828swap=true := by decide +kernel
theorem certified0828swap : Certified (graph core0828) (root 8) 1 0 :=
  of_native_maps core0828 DegreeOneSmallSpectrum550.graph DegreeOneSmallSpectrum395.graph
    sourceMap0828swap fusedMap0828swap sourceMap0828swap_checked fusedMap0828swap_checked
    DegreeOneSmallComparisons.comparison0828
#print axioms sourceMap0828swap_checked
#print axioms fusedMap0828swap_checked
#print axioms certified0828swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
