/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0346 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0346 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0346 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0346_checked : acceptsGraphIso
    (source (graph core0346) (root 6) 1 3) DegreeOneSmallSpectrum1347.graph sourceMap0346=true := by decide +kernel
theorem fusedMap0346_checked : acceptsGraphIso
    (fused (graph core0346) (root 6) 1 3) DegreeOneSmallSpectrum915.graph fusedMap0346=true := by decide +kernel
theorem certified0346 : Certified (graph core0346) (root 6) 1 3 :=
  of_native_maps core0346 DegreeOneSmallSpectrum1347.graph DegreeOneSmallSpectrum915.graph
    sourceMap0346 fusedMap0346 sourceMap0346_checked fusedMap0346_checked
    DegreeOneSmallComparisons.comparison0346
#print axioms sourceMap0346_checked
#print axioms fusedMap0346_checked
#print axioms certified0346
def sourceMap0346swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0346swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0346swap_checked : acceptsGraphIso
    (source (graph core0346) (root 6) 3 1) DegreeOneSmallSpectrum1347.graph sourceMap0346swap=true := by decide +kernel
theorem fusedMap0346swap_checked : acceptsGraphIso
    (fused (graph core0346) (root 6) 3 1) DegreeOneSmallSpectrum915.graph fusedMap0346swap=true := by decide +kernel
theorem certified0346swap : Certified (graph core0346) (root 6) 3 1 :=
  of_native_maps core0346 DegreeOneSmallSpectrum1347.graph DegreeOneSmallSpectrum915.graph
    sourceMap0346swap fusedMap0346swap sourceMap0346swap_checked fusedMap0346swap_checked
    DegreeOneSmallComparisons.comparison0346
#print axioms sourceMap0346swap_checked
#print axioms fusedMap0346swap_checked
#print axioms certified0346swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
