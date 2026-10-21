/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0364 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0364 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0364 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0364_checked : acceptsGraphIso
    (source (graph core0364) (root 6) 1 3) DegreeOneSmallSpectrum1434.graph sourceMap0364=true := by decide +kernel
theorem fusedMap0364_checked : acceptsGraphIso
    (fused (graph core0364) (root 6) 1 3) DegreeOneSmallSpectrum929.graph fusedMap0364=true := by decide +kernel
theorem certified0364 : Certified (graph core0364) (root 6) 1 3 :=
  of_native_maps core0364 DegreeOneSmallSpectrum1434.graph DegreeOneSmallSpectrum929.graph
    sourceMap0364 fusedMap0364 sourceMap0364_checked fusedMap0364_checked
    DegreeOneSmallComparisons.comparison0364
#print axioms sourceMap0364_checked
#print axioms fusedMap0364_checked
#print axioms certified0364
def sourceMap0364swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0364swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0364swap_checked : acceptsGraphIso
    (source (graph core0364) (root 6) 3 1) DegreeOneSmallSpectrum1434.graph sourceMap0364swap=true := by decide +kernel
theorem fusedMap0364swap_checked : acceptsGraphIso
    (fused (graph core0364) (root 6) 3 1) DegreeOneSmallSpectrum929.graph fusedMap0364swap=true := by decide +kernel
theorem certified0364swap : Certified (graph core0364) (root 6) 3 1 :=
  of_native_maps core0364 DegreeOneSmallSpectrum1434.graph DegreeOneSmallSpectrum929.graph
    sourceMap0364swap fusedMap0364swap sourceMap0364swap_checked fusedMap0364swap_checked
    DegreeOneSmallComparisons.comparison0364
#print axioms sourceMap0364swap_checked
#print axioms fusedMap0364swap_checked
#print axioms certified0364swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
