/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0045 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0045 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (sourceLabel 2 1 7 v)
def fusedMap0045 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 1 7 v)
theorem sourceMap0045_checked : acceptsGraphIso
    (source (graph core0045) (root 2) 1 7) DegreeOneSmallSpectrum915.graph sourceMap0045=true := by decide +kernel
theorem fusedMap0045_checked : acceptsGraphIso
    (fused (graph core0045) (root 2) 1 7) DegreeOneSmallSpectrum861.graph fusedMap0045=true := by decide +kernel
theorem certified0045 : Certified (graph core0045) (root 2) 1 7 :=
  of_native_maps core0045 DegreeOneSmallSpectrum915.graph DegreeOneSmallSpectrum861.graph
    sourceMap0045 fusedMap0045 sourceMap0045_checked fusedMap0045_checked
    DegreeOneSmallComparisons.comparison0045
#print axioms sourceMap0045_checked
#print axioms fusedMap0045_checked
#print axioms certified0045
def sourceMap0045swap : (Vertices 2 ⊕ Fin 8 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,4,5,2,1,0,8,9,10,11,12,6,7] (sourceLabel 2 7 1 v)
def fusedMap0045swap : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 7 1 v)
theorem sourceMap0045swap_checked : acceptsGraphIso
    (source (graph core0045) (root 2) 7 1) DegreeOneSmallSpectrum915.graph sourceMap0045swap=true := by decide +kernel
theorem fusedMap0045swap_checked : acceptsGraphIso
    (fused (graph core0045) (root 2) 7 1) DegreeOneSmallSpectrum861.graph fusedMap0045swap=true := by decide +kernel
theorem certified0045swap : Certified (graph core0045) (root 2) 7 1 :=
  of_native_maps core0045 DegreeOneSmallSpectrum915.graph DegreeOneSmallSpectrum861.graph
    sourceMap0045swap fusedMap0045swap sourceMap0045swap_checked fusedMap0045swap_checked
    DegreeOneSmallComparisons.comparison0045
#print axioms sourceMap0045swap_checked
#print axioms fusedMap0045swap_checked
#print axioms certified0045swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
