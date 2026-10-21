/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0634 : Family 7 := level7.get ⟨45,by decide⟩
def sourceMap0634 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0634 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0634_checked : acceptsGraphIso
    (source (graph core0634) (root 7) 0 1) DegreeOneSmallSpectrum339.graph sourceMap0634=true := by decide +kernel
theorem fusedMap0634_checked : acceptsGraphIso
    (fused (graph core0634) (root 7) 0 1) DegreeOneSmallSpectrum208.graph fusedMap0634=true := by decide +kernel
theorem certified0634 : Certified (graph core0634) (root 7) 0 1 :=
  of_native_maps core0634 DegreeOneSmallSpectrum339.graph DegreeOneSmallSpectrum208.graph
    sourceMap0634 fusedMap0634 sourceMap0634_checked fusedMap0634_checked
    DegreeOneSmallComparisons.comparison0634
#print axioms sourceMap0634_checked
#print axioms fusedMap0634_checked
#print axioms certified0634
def sourceMap0634swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0634swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0634swap_checked : acceptsGraphIso
    (source (graph core0634) (root 7) 1 0) DegreeOneSmallSpectrum339.graph sourceMap0634swap=true := by decide +kernel
theorem fusedMap0634swap_checked : acceptsGraphIso
    (fused (graph core0634) (root 7) 1 0) DegreeOneSmallSpectrum208.graph fusedMap0634swap=true := by decide +kernel
theorem certified0634swap : Certified (graph core0634) (root 7) 1 0 :=
  of_native_maps core0634 DegreeOneSmallSpectrum339.graph DegreeOneSmallSpectrum208.graph
    sourceMap0634swap fusedMap0634swap sourceMap0634swap_checked fusedMap0634swap_checked
    DegreeOneSmallComparisons.comparison0634
#print axioms sourceMap0634swap_checked
#print axioms fusedMap0634swap_checked
#print axioms certified0634swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
