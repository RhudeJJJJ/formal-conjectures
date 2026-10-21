/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0236 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0236 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap0236 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap0236_checked : acceptsGraphIso
    (source (graph core0236) (root 5) 0 5) DegreeOneSmallSpectrum910.graph sourceMap0236=true := by decide +kernel
theorem fusedMap0236_checked : acceptsGraphIso
    (fused (graph core0236) (root 5) 0 5) DegreeOneSmallSpectrum915.graph fusedMap0236=true := by decide +kernel
theorem certified0236 : Certified (graph core0236) (root 5) 0 5 :=
  of_native_maps core0236 DegreeOneSmallSpectrum910.graph DegreeOneSmallSpectrum915.graph
    sourceMap0236 fusedMap0236 sourceMap0236_checked fusedMap0236_checked
    DegreeOneSmallComparisons.comparison0236
#print axioms sourceMap0236_checked
#print axioms fusedMap0236_checked
#print axioms certified0236
def sourceMap0236swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap0236swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap0236swap_checked : acceptsGraphIso
    (source (graph core0236) (root 5) 5 0) DegreeOneSmallSpectrum910.graph sourceMap0236swap=true := by decide +kernel
theorem fusedMap0236swap_checked : acceptsGraphIso
    (fused (graph core0236) (root 5) 5 0) DegreeOneSmallSpectrum915.graph fusedMap0236swap=true := by decide +kernel
theorem certified0236swap : Certified (graph core0236) (root 5) 5 0 :=
  of_native_maps core0236 DegreeOneSmallSpectrum910.graph DegreeOneSmallSpectrum915.graph
    sourceMap0236swap fusedMap0236swap sourceMap0236swap_checked fusedMap0236swap_checked
    DegreeOneSmallComparisons.comparison0236
#print axioms sourceMap0236swap_checked
#print axioms fusedMap0236swap_checked
#print axioms certified0236swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
