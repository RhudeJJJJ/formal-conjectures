/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0458 : Family 7 := level7.get ⟨1,by decide⟩
def sourceMap0458 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0458 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0458_checked : acceptsGraphIso
    (source (graph core0458) (root 7) 1 2) DegreeOneSmallSpectrum901.graph sourceMap0458=true := by decide +kernel
theorem fusedMap0458_checked : acceptsGraphIso
    (fused (graph core0458) (root 7) 1 2) DegreeOneSmallSpectrum856.graph fusedMap0458=true := by decide +kernel
theorem certified0458 : Certified (graph core0458) (root 7) 1 2 :=
  of_native_maps core0458 DegreeOneSmallSpectrum901.graph DegreeOneSmallSpectrum856.graph
    sourceMap0458 fusedMap0458 sourceMap0458_checked fusedMap0458_checked
    DegreeOneSmallComparisons.comparison0458
#print axioms sourceMap0458_checked
#print axioms fusedMap0458_checked
#print axioms certified0458
def sourceMap0458swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0458swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0458swap_checked : acceptsGraphIso
    (source (graph core0458) (root 7) 2 1) DegreeOneSmallSpectrum901.graph sourceMap0458swap=true := by decide +kernel
theorem fusedMap0458swap_checked : acceptsGraphIso
    (fused (graph core0458) (root 7) 2 1) DegreeOneSmallSpectrum856.graph fusedMap0458swap=true := by decide +kernel
theorem certified0458swap : Certified (graph core0458) (root 7) 2 1 :=
  of_native_maps core0458 DegreeOneSmallSpectrum901.graph DegreeOneSmallSpectrum856.graph
    sourceMap0458swap fusedMap0458swap sourceMap0458swap_checked fusedMap0458swap_checked
    DegreeOneSmallComparisons.comparison0458
#print axioms sourceMap0458swap_checked
#print axioms fusedMap0458swap_checked
#print axioms certified0458swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
