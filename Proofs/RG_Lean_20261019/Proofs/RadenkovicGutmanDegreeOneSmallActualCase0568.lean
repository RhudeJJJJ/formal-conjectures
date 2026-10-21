/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0568 : Family 7 := level7.get ⟨27,by decide⟩
def sourceMap0568 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0568 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0568_checked : acceptsGraphIso
    (source (graph core0568) (root 7) 0 1) DegreeOneSmallSpectrum257.graph sourceMap0568=true := by decide +kernel
theorem fusedMap0568_checked : acceptsGraphIso
    (fused (graph core0568) (root 7) 0 1) DegreeOneSmallSpectrum170.graph fusedMap0568=true := by decide +kernel
theorem certified0568 : Certified (graph core0568) (root 7) 0 1 :=
  of_native_maps core0568 DegreeOneSmallSpectrum257.graph DegreeOneSmallSpectrum170.graph
    sourceMap0568 fusedMap0568 sourceMap0568_checked fusedMap0568_checked
    DegreeOneSmallComparisons.comparison0568
#print axioms sourceMap0568_checked
#print axioms fusedMap0568_checked
#print axioms certified0568
def sourceMap0568swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0568swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0568swap_checked : acceptsGraphIso
    (source (graph core0568) (root 7) 1 0) DegreeOneSmallSpectrum257.graph sourceMap0568swap=true := by decide +kernel
theorem fusedMap0568swap_checked : acceptsGraphIso
    (fused (graph core0568) (root 7) 1 0) DegreeOneSmallSpectrum170.graph fusedMap0568swap=true := by decide +kernel
theorem certified0568swap : Certified (graph core0568) (root 7) 1 0 :=
  of_native_maps core0568 DegreeOneSmallSpectrum257.graph DegreeOneSmallSpectrum170.graph
    sourceMap0568swap fusedMap0568swap sourceMap0568swap_checked fusedMap0568swap_checked
    DegreeOneSmallComparisons.comparison0568
#print axioms sourceMap0568swap_checked
#print axioms fusedMap0568swap_checked
#print axioms certified0568swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
