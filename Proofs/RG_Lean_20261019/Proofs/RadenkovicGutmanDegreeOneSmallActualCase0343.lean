/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0343 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0343 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0343 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0343_checked : acceptsGraphIso
    (source (graph core0343) (root 6) 0 4) DegreeOneSmallSpectrum911.graph sourceMap0343=true := by decide +kernel
theorem fusedMap0343_checked : acceptsGraphIso
    (fused (graph core0343) (root 6) 0 4) DegreeOneSmallSpectrum915.graph fusedMap0343=true := by decide +kernel
theorem certified0343 : Certified (graph core0343) (root 6) 0 4 :=
  of_native_maps core0343 DegreeOneSmallSpectrum911.graph DegreeOneSmallSpectrum915.graph
    sourceMap0343 fusedMap0343 sourceMap0343_checked fusedMap0343_checked
    DegreeOneSmallComparisons.comparison0343
#print axioms sourceMap0343_checked
#print axioms fusedMap0343_checked
#print axioms certified0343
def sourceMap0343swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap0343swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0343swap_checked : acceptsGraphIso
    (source (graph core0343) (root 6) 4 0) DegreeOneSmallSpectrum911.graph sourceMap0343swap=true := by decide +kernel
theorem fusedMap0343swap_checked : acceptsGraphIso
    (fused (graph core0343) (root 6) 4 0) DegreeOneSmallSpectrum915.graph fusedMap0343swap=true := by decide +kernel
theorem certified0343swap : Certified (graph core0343) (root 6) 4 0 :=
  of_native_maps core0343 DegreeOneSmallSpectrum911.graph DegreeOneSmallSpectrum915.graph
    sourceMap0343swap fusedMap0343swap sourceMap0343swap_checked fusedMap0343swap_checked
    DegreeOneSmallComparisons.comparison0343
#print axioms sourceMap0343swap_checked
#print axioms fusedMap0343swap_checked
#print axioms certified0343swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
