/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0512 : Family 7 := level7.get ⟨12,by decide⟩
def sourceMap0512 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0512 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0512_checked : acceptsGraphIso
    (source (graph core0512) (root 7) 1 2) DegreeOneSmallSpectrum1343.graph sourceMap0512=true := by decide +kernel
theorem fusedMap0512_checked : acceptsGraphIso
    (fused (graph core0512) (root 7) 1 2) DegreeOneSmallSpectrum915.graph fusedMap0512=true := by decide +kernel
theorem certified0512 : Certified (graph core0512) (root 7) 1 2 :=
  of_native_maps core0512 DegreeOneSmallSpectrum1343.graph DegreeOneSmallSpectrum915.graph
    sourceMap0512 fusedMap0512 sourceMap0512_checked fusedMap0512_checked
    DegreeOneSmallComparisons.comparison0512
#print axioms sourceMap0512_checked
#print axioms fusedMap0512_checked
#print axioms certified0512
def sourceMap0512swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0512swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0512swap_checked : acceptsGraphIso
    (source (graph core0512) (root 7) 2 1) DegreeOneSmallSpectrum1343.graph sourceMap0512swap=true := by decide +kernel
theorem fusedMap0512swap_checked : acceptsGraphIso
    (fused (graph core0512) (root 7) 2 1) DegreeOneSmallSpectrum915.graph fusedMap0512swap=true := by decide +kernel
theorem certified0512swap : Certified (graph core0512) (root 7) 2 1 :=
  of_native_maps core0512 DegreeOneSmallSpectrum1343.graph DegreeOneSmallSpectrum915.graph
    sourceMap0512swap fusedMap0512swap sourceMap0512swap_checked fusedMap0512swap_checked
    DegreeOneSmallComparisons.comparison0512
#print axioms sourceMap0512swap_checked
#print axioms fusedMap0512swap_checked
#print axioms certified0512swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
