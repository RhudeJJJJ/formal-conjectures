/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0526 : Family 7 := level7.get ⟨15,by decide⟩
def sourceMap0526 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0526 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (fusedLabel 7 0 1 v)
theorem sourceMap0526_checked : acceptsGraphIso
    (source (graph core0526) (root 7) 0 1) DegreeOneSmallSpectrum210.graph sourceMap0526=true := by decide +kernel
theorem fusedMap0526_checked : acceptsGraphIso
    (fused (graph core0526) (root 7) 0 1) DegreeOneSmallSpectrum217.graph fusedMap0526=true := by decide +kernel
theorem certified0526 : Certified (graph core0526) (root 7) 0 1 :=
  of_native_maps core0526 DegreeOneSmallSpectrum210.graph DegreeOneSmallSpectrum217.graph
    sourceMap0526 fusedMap0526 sourceMap0526_checked fusedMap0526_checked
    DegreeOneSmallComparisons.comparison0526
#print axioms sourceMap0526_checked
#print axioms fusedMap0526_checked
#print axioms certified0526
def sourceMap0526swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0526swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (fusedLabel 7 1 0 v)
theorem sourceMap0526swap_checked : acceptsGraphIso
    (source (graph core0526) (root 7) 1 0) DegreeOneSmallSpectrum210.graph sourceMap0526swap=true := by decide +kernel
theorem fusedMap0526swap_checked : acceptsGraphIso
    (fused (graph core0526) (root 7) 1 0) DegreeOneSmallSpectrum217.graph fusedMap0526swap=true := by decide +kernel
theorem certified0526swap : Certified (graph core0526) (root 7) 1 0 :=
  of_native_maps core0526 DegreeOneSmallSpectrum210.graph DegreeOneSmallSpectrum217.graph
    sourceMap0526swap fusedMap0526swap sourceMap0526swap_checked fusedMap0526swap_checked
    DegreeOneSmallComparisons.comparison0526
#print axioms sourceMap0526swap_checked
#print axioms fusedMap0526swap_checked
#print axioms certified0526swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
