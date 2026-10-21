/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0539 : Family 7 := level7.get ⟨18,by decide⟩
def sourceMap0539 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0539 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0539_checked : acceptsGraphIso
    (source (graph core0539) (root 7) 0 2) DegreeOneSmallSpectrum580.graph sourceMap0539=true := by decide +kernel
theorem fusedMap0539_checked : acceptsGraphIso
    (fused (graph core0539) (root 7) 0 2) DegreeOneSmallSpectrum388.graph fusedMap0539=true := by decide +kernel
theorem certified0539 : Certified (graph core0539) (root 7) 0 2 :=
  of_native_maps core0539 DegreeOneSmallSpectrum580.graph DegreeOneSmallSpectrum388.graph
    sourceMap0539 fusedMap0539 sourceMap0539_checked fusedMap0539_checked
    DegreeOneSmallComparisons.comparison0539
#print axioms sourceMap0539_checked
#print axioms fusedMap0539_checked
#print axioms certified0539
def sourceMap0539swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0539swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0539swap_checked : acceptsGraphIso
    (source (graph core0539) (root 7) 2 0) DegreeOneSmallSpectrum580.graph sourceMap0539swap=true := by decide +kernel
theorem fusedMap0539swap_checked : acceptsGraphIso
    (fused (graph core0539) (root 7) 2 0) DegreeOneSmallSpectrum388.graph fusedMap0539swap=true := by decide +kernel
theorem certified0539swap : Certified (graph core0539) (root 7) 2 0 :=
  of_native_maps core0539 DegreeOneSmallSpectrum580.graph DegreeOneSmallSpectrum388.graph
    sourceMap0539swap fusedMap0539swap sourceMap0539swap_checked fusedMap0539swap_checked
    DegreeOneSmallComparisons.comparison0539
#print axioms sourceMap0539swap_checked
#print axioms fusedMap0539swap_checked
#print axioms certified0539swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
