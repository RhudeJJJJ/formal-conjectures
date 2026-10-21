/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0596 : Family 7 := level7.get ⟨32,by decide⟩
def sourceMap0596 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0596 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0596_checked : acceptsGraphIso
    (source (graph core0596) (root 7) 1 2) DegreeOneSmallSpectrum1155.graph sourceMap0596=true := by decide +kernel
theorem fusedMap0596_checked : acceptsGraphIso
    (fused (graph core0596) (root 7) 1 2) DegreeOneSmallSpectrum873.graph fusedMap0596=true := by decide +kernel
theorem certified0596 : Certified (graph core0596) (root 7) 1 2 :=
  of_native_maps core0596 DegreeOneSmallSpectrum1155.graph DegreeOneSmallSpectrum873.graph
    sourceMap0596 fusedMap0596 sourceMap0596_checked fusedMap0596_checked
    DegreeOneSmallComparisons.comparison0596
#print axioms sourceMap0596_checked
#print axioms fusedMap0596_checked
#print axioms certified0596
def sourceMap0596swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0596swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0596swap_checked : acceptsGraphIso
    (source (graph core0596) (root 7) 2 1) DegreeOneSmallSpectrum1155.graph sourceMap0596swap=true := by decide +kernel
theorem fusedMap0596swap_checked : acceptsGraphIso
    (fused (graph core0596) (root 7) 2 1) DegreeOneSmallSpectrum873.graph fusedMap0596swap=true := by decide +kernel
theorem certified0596swap : Certified (graph core0596) (root 7) 2 1 :=
  of_native_maps core0596 DegreeOneSmallSpectrum1155.graph DegreeOneSmallSpectrum873.graph
    sourceMap0596swap fusedMap0596swap sourceMap0596swap_checked fusedMap0596swap_checked
    DegreeOneSmallComparisons.comparison0596
#print axioms sourceMap0596swap_checked
#print axioms fusedMap0596swap_checked
#print axioms certified0596swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
