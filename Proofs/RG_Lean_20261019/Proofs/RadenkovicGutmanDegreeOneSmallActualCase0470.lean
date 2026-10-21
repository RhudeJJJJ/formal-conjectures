/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0470 : Family 7 := level7.get ⟨3,by decide⟩
def sourceMap0470 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 7 1 2 v)
def fusedMap0470 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0470_checked : acceptsGraphIso
    (source (graph core0470) (root 7) 1 2) DegreeOneSmallSpectrum949.graph sourceMap0470=true := by decide +kernel
theorem fusedMap0470_checked : acceptsGraphIso
    (fused (graph core0470) (root 7) 1 2) DegreeOneSmallSpectrum858.graph fusedMap0470=true := by decide +kernel
theorem certified0470 : Certified (graph core0470) (root 7) 1 2 :=
  of_native_maps core0470 DegreeOneSmallSpectrum949.graph DegreeOneSmallSpectrum858.graph
    sourceMap0470 fusedMap0470 sourceMap0470_checked fusedMap0470_checked
    DegreeOneSmallComparisons.comparison0470
#print axioms sourceMap0470_checked
#print axioms fusedMap0470_checked
#print axioms certified0470
def sourceMap0470swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 2 1 v)
def fusedMap0470swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0470swap_checked : acceptsGraphIso
    (source (graph core0470) (root 7) 2 1) DegreeOneSmallSpectrum949.graph sourceMap0470swap=true := by decide +kernel
theorem fusedMap0470swap_checked : acceptsGraphIso
    (fused (graph core0470) (root 7) 2 1) DegreeOneSmallSpectrum858.graph fusedMap0470swap=true := by decide +kernel
theorem certified0470swap : Certified (graph core0470) (root 7) 2 1 :=
  of_native_maps core0470 DegreeOneSmallSpectrum949.graph DegreeOneSmallSpectrum858.graph
    sourceMap0470swap fusedMap0470swap sourceMap0470swap_checked fusedMap0470swap_checked
    DegreeOneSmallComparisons.comparison0470
#print axioms sourceMap0470swap_checked
#print axioms fusedMap0470swap_checked
#print axioms certified0470swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
