/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0576 : Family 7 := level7.get ⟨28,by decide⟩
def sourceMap0576 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0576 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0576_checked : acceptsGraphIso
    (source (graph core0576) (root 7) 0 3) DegreeOneSmallSpectrum1059.graph sourceMap0576=true := by decide +kernel
theorem fusedMap0576_checked : acceptsGraphIso
    (fused (graph core0576) (root 7) 0 3) DegreeOneSmallSpectrum864.graph fusedMap0576=true := by decide +kernel
theorem certified0576 : Certified (graph core0576) (root 7) 0 3 :=
  of_native_maps core0576 DegreeOneSmallSpectrum1059.graph DegreeOneSmallSpectrum864.graph
    sourceMap0576 fusedMap0576 sourceMap0576_checked fusedMap0576_checked
    DegreeOneSmallComparisons.comparison0576
#print axioms sourceMap0576_checked
#print axioms fusedMap0576_checked
#print axioms certified0576
def sourceMap0576swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0576swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0576swap_checked : acceptsGraphIso
    (source (graph core0576) (root 7) 3 0) DegreeOneSmallSpectrum1059.graph sourceMap0576swap=true := by decide +kernel
theorem fusedMap0576swap_checked : acceptsGraphIso
    (fused (graph core0576) (root 7) 3 0) DegreeOneSmallSpectrum864.graph fusedMap0576swap=true := by decide +kernel
theorem certified0576swap : Certified (graph core0576) (root 7) 3 0 :=
  of_native_maps core0576 DegreeOneSmallSpectrum1059.graph DegreeOneSmallSpectrum864.graph
    sourceMap0576swap fusedMap0576swap sourceMap0576swap_checked fusedMap0576swap_checked
    DegreeOneSmallComparisons.comparison0576
#print axioms sourceMap0576swap_checked
#print axioms fusedMap0576swap_checked
#print axioms certified0576swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
