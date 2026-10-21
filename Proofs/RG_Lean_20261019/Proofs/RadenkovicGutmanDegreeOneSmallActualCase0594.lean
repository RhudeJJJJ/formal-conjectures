/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0594 : Family 7 := level7.get ⟨32,by decide⟩
def sourceMap0594 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0594 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0594_checked : acceptsGraphIso
    (source (graph core0594) (root 7) 0 3) DegreeOneSmallSpectrum1158.graph sourceMap0594=true := by decide +kernel
theorem fusedMap0594_checked : acceptsGraphIso
    (fused (graph core0594) (root 7) 0 3) DegreeOneSmallSpectrum873.graph fusedMap0594=true := by decide +kernel
theorem certified0594 : Certified (graph core0594) (root 7) 0 3 :=
  of_native_maps core0594 DegreeOneSmallSpectrum1158.graph DegreeOneSmallSpectrum873.graph
    sourceMap0594 fusedMap0594 sourceMap0594_checked fusedMap0594_checked
    DegreeOneSmallComparisons.comparison0594
#print axioms sourceMap0594_checked
#print axioms fusedMap0594_checked
#print axioms certified0594
def sourceMap0594swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0594swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0594swap_checked : acceptsGraphIso
    (source (graph core0594) (root 7) 3 0) DegreeOneSmallSpectrum1158.graph sourceMap0594swap=true := by decide +kernel
theorem fusedMap0594swap_checked : acceptsGraphIso
    (fused (graph core0594) (root 7) 3 0) DegreeOneSmallSpectrum873.graph fusedMap0594swap=true := by decide +kernel
theorem certified0594swap : Certified (graph core0594) (root 7) 3 0 :=
  of_native_maps core0594 DegreeOneSmallSpectrum1158.graph DegreeOneSmallSpectrum873.graph
    sourceMap0594swap fusedMap0594swap sourceMap0594swap_checked fusedMap0594swap_checked
    DegreeOneSmallComparisons.comparison0594
#print axioms sourceMap0594swap_checked
#print axioms fusedMap0594swap_checked
#print axioms certified0594swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
