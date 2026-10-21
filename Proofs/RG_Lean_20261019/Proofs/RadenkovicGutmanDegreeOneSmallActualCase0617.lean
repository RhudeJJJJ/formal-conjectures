/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0617 : Family 7 := level7.get ⟨40,by decide⟩
def sourceMap0617 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0617 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0617_checked : acceptsGraphIso
    (source (graph core0617) (root 7) 0 2) DegreeOneSmallSpectrum509.graph sourceMap0617=true := by decide +kernel
theorem fusedMap0617_checked : acceptsGraphIso
    (fused (graph core0617) (root 7) 0 2) DegreeOneSmallSpectrum510.graph fusedMap0617=true := by decide +kernel
theorem certified0617 : Certified (graph core0617) (root 7) 0 2 :=
  of_native_maps core0617 DegreeOneSmallSpectrum509.graph DegreeOneSmallSpectrum510.graph
    sourceMap0617 fusedMap0617 sourceMap0617_checked fusedMap0617_checked
    DegreeOneSmallComparisons.comparison0617
#print axioms sourceMap0617_checked
#print axioms fusedMap0617_checked
#print axioms certified0617
def sourceMap0617swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0617swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0617swap_checked : acceptsGraphIso
    (source (graph core0617) (root 7) 2 0) DegreeOneSmallSpectrum509.graph sourceMap0617swap=true := by decide +kernel
theorem fusedMap0617swap_checked : acceptsGraphIso
    (fused (graph core0617) (root 7) 2 0) DegreeOneSmallSpectrum510.graph fusedMap0617swap=true := by decide +kernel
theorem certified0617swap : Certified (graph core0617) (root 7) 2 0 :=
  of_native_maps core0617 DegreeOneSmallSpectrum509.graph DegreeOneSmallSpectrum510.graph
    sourceMap0617swap fusedMap0617swap sourceMap0617swap_checked fusedMap0617swap_checked
    DegreeOneSmallComparisons.comparison0617
#print axioms sourceMap0617swap_checked
#print axioms fusedMap0617swap_checked
#print axioms certified0617swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
