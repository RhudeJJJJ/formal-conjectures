/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0468 : Family 7 := level7.get ⟨3,by decide⟩
def sourceMap0468 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0468 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0468_checked : acceptsGraphIso
    (source (graph core0468) (root 7) 0 3) DegreeOneSmallSpectrum965.graph sourceMap0468=true := by decide +kernel
theorem fusedMap0468_checked : acceptsGraphIso
    (fused (graph core0468) (root 7) 0 3) DegreeOneSmallSpectrum858.graph fusedMap0468=true := by decide +kernel
theorem certified0468 : Certified (graph core0468) (root 7) 0 3 :=
  of_native_maps core0468 DegreeOneSmallSpectrum965.graph DegreeOneSmallSpectrum858.graph
    sourceMap0468 fusedMap0468 sourceMap0468_checked fusedMap0468_checked
    DegreeOneSmallComparisons.comparison0468
#print axioms sourceMap0468_checked
#print axioms fusedMap0468_checked
#print axioms certified0468
def sourceMap0468swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0468swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0468swap_checked : acceptsGraphIso
    (source (graph core0468) (root 7) 3 0) DegreeOneSmallSpectrum965.graph sourceMap0468swap=true := by decide +kernel
theorem fusedMap0468swap_checked : acceptsGraphIso
    (fused (graph core0468) (root 7) 3 0) DegreeOneSmallSpectrum858.graph fusedMap0468swap=true := by decide +kernel
theorem certified0468swap : Certified (graph core0468) (root 7) 3 0 :=
  of_native_maps core0468 DegreeOneSmallSpectrum965.graph DegreeOneSmallSpectrum858.graph
    sourceMap0468swap fusedMap0468swap sourceMap0468swap_checked fusedMap0468swap_checked
    DegreeOneSmallComparisons.comparison0468
#print axioms sourceMap0468swap_checked
#print axioms fusedMap0468swap_checked
#print axioms certified0468swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
