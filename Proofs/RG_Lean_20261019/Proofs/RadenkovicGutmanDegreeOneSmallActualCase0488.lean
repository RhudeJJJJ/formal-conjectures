/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0488 : Family 7 := level7.get ⟨7,by decide⟩
def sourceMap0488 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0488 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0488_checked : acceptsGraphIso
    (source (graph core0488) (root 7) 1 2) DegreeOneSmallSpectrum1077.graph sourceMap0488=true := by decide +kernel
theorem fusedMap0488_checked : acceptsGraphIso
    (fused (graph core0488) (root 7) 1 2) DegreeOneSmallSpectrum870.graph fusedMap0488=true := by decide +kernel
theorem certified0488 : Certified (graph core0488) (root 7) 1 2 :=
  of_native_maps core0488 DegreeOneSmallSpectrum1077.graph DegreeOneSmallSpectrum870.graph
    sourceMap0488 fusedMap0488 sourceMap0488_checked fusedMap0488_checked
    DegreeOneSmallComparisons.comparison0488
#print axioms sourceMap0488_checked
#print axioms fusedMap0488_checked
#print axioms certified0488
def sourceMap0488swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0488swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0488swap_checked : acceptsGraphIso
    (source (graph core0488) (root 7) 2 1) DegreeOneSmallSpectrum1077.graph sourceMap0488swap=true := by decide +kernel
theorem fusedMap0488swap_checked : acceptsGraphIso
    (fused (graph core0488) (root 7) 2 1) DegreeOneSmallSpectrum870.graph fusedMap0488swap=true := by decide +kernel
theorem certified0488swap : Certified (graph core0488) (root 7) 2 1 :=
  of_native_maps core0488 DegreeOneSmallSpectrum1077.graph DegreeOneSmallSpectrum870.graph
    sourceMap0488swap fusedMap0488swap sourceMap0488swap_checked fusedMap0488swap_checked
    DegreeOneSmallComparisons.comparison0488
#print axioms sourceMap0488swap_checked
#print axioms fusedMap0488swap_checked
#print axioms certified0488swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
