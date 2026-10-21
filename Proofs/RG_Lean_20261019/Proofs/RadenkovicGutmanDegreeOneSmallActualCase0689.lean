/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0689 : Family 7 := level7.get ⟨66,by decide⟩
def sourceMap0689 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0689 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0689_checked : acceptsGraphIso
    (source (graph core0689) (root 7) 0 2) DegreeOneSmallSpectrum649.graph sourceMap0689=true := by decide +kernel
theorem fusedMap0689_checked : acceptsGraphIso
    (fused (graph core0689) (root 7) 0 2) DegreeOneSmallSpectrum406.graph fusedMap0689=true := by decide +kernel
theorem certified0689 : Certified (graph core0689) (root 7) 0 2 :=
  of_native_maps core0689 DegreeOneSmallSpectrum649.graph DegreeOneSmallSpectrum406.graph
    sourceMap0689 fusedMap0689 sourceMap0689_checked fusedMap0689_checked
    DegreeOneSmallComparisons.comparison0689
#print axioms sourceMap0689_checked
#print axioms fusedMap0689_checked
#print axioms certified0689
def sourceMap0689swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0689swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0689swap_checked : acceptsGraphIso
    (source (graph core0689) (root 7) 2 0) DegreeOneSmallSpectrum649.graph sourceMap0689swap=true := by decide +kernel
theorem fusedMap0689swap_checked : acceptsGraphIso
    (fused (graph core0689) (root 7) 2 0) DegreeOneSmallSpectrum406.graph fusedMap0689swap=true := by decide +kernel
theorem certified0689swap : Certified (graph core0689) (root 7) 2 0 :=
  of_native_maps core0689 DegreeOneSmallSpectrum649.graph DegreeOneSmallSpectrum406.graph
    sourceMap0689swap fusedMap0689swap sourceMap0689swap_checked fusedMap0689swap_checked
    DegreeOneSmallComparisons.comparison0689
#print axioms sourceMap0689swap_checked
#print axioms fusedMap0689swap_checked
#print axioms certified0689swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
