/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0566 : Family 7 := level7.get ⟨26,by decide⟩
def sourceMap0566 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0566 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0566_checked : acceptsGraphIso
    (source (graph core0566) (root 7) 1 2) DegreeOneSmallSpectrum1005.graph sourceMap0566=true := by decide +kernel
theorem fusedMap0566_checked : acceptsGraphIso
    (fused (graph core0566) (root 7) 1 2) DegreeOneSmallSpectrum862.graph fusedMap0566=true := by decide +kernel
theorem certified0566 : Certified (graph core0566) (root 7) 1 2 :=
  of_native_maps core0566 DegreeOneSmallSpectrum1005.graph DegreeOneSmallSpectrum862.graph
    sourceMap0566 fusedMap0566 sourceMap0566_checked fusedMap0566_checked
    DegreeOneSmallComparisons.comparison0566
#print axioms sourceMap0566_checked
#print axioms fusedMap0566_checked
#print axioms certified0566
def sourceMap0566swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0566swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0566swap_checked : acceptsGraphIso
    (source (graph core0566) (root 7) 2 1) DegreeOneSmallSpectrum1005.graph sourceMap0566swap=true := by decide +kernel
theorem fusedMap0566swap_checked : acceptsGraphIso
    (fused (graph core0566) (root 7) 2 1) DegreeOneSmallSpectrum862.graph fusedMap0566swap=true := by decide +kernel
theorem certified0566swap : Certified (graph core0566) (root 7) 2 1 :=
  of_native_maps core0566 DegreeOneSmallSpectrum1005.graph DegreeOneSmallSpectrum862.graph
    sourceMap0566swap fusedMap0566swap sourceMap0566swap_checked fusedMap0566swap_checked
    DegreeOneSmallComparisons.comparison0566
#print axioms sourceMap0566swap_checked
#print axioms fusedMap0566swap_checked
#print axioms certified0566swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
