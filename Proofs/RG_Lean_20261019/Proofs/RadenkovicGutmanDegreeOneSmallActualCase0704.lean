/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0704 : Family 7 := level7.get ⟨71,by decide⟩
def sourceMap0704 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0704 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0704_checked : acceptsGraphIso
    (source (graph core0704) (root 7) 1 2) DegreeOneSmallSpectrum1753.graph sourceMap0704=true := by decide +kernel
theorem fusedMap0704_checked : acceptsGraphIso
    (fused (graph core0704) (root 7) 1 2) DegreeOneSmallSpectrum1095.graph fusedMap0704=true := by decide +kernel
theorem certified0704 : Certified (graph core0704) (root 7) 1 2 :=
  of_native_maps core0704 DegreeOneSmallSpectrum1753.graph DegreeOneSmallSpectrum1095.graph
    sourceMap0704 fusedMap0704 sourceMap0704_checked fusedMap0704_checked
    DegreeOneSmallComparisons.comparison0704
#print axioms sourceMap0704_checked
#print axioms fusedMap0704_checked
#print axioms certified0704
def sourceMap0704swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0704swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0704swap_checked : acceptsGraphIso
    (source (graph core0704) (root 7) 2 1) DegreeOneSmallSpectrum1753.graph sourceMap0704swap=true := by decide +kernel
theorem fusedMap0704swap_checked : acceptsGraphIso
    (fused (graph core0704) (root 7) 2 1) DegreeOneSmallSpectrum1095.graph fusedMap0704swap=true := by decide +kernel
theorem certified0704swap : Certified (graph core0704) (root 7) 2 1 :=
  of_native_maps core0704 DegreeOneSmallSpectrum1753.graph DegreeOneSmallSpectrum1095.graph
    sourceMap0704swap fusedMap0704swap sourceMap0704swap_checked fusedMap0704swap_checked
    DegreeOneSmallComparisons.comparison0704
#print axioms sourceMap0704swap_checked
#print axioms fusedMap0704swap_checked
#print axioms certified0704swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
