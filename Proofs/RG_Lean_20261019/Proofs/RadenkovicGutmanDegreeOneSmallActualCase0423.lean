/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0423 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0423 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap0423 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0423_checked : acceptsGraphIso
    (source (graph core0423) (root 6) 0 3) DegreeOneSmallSpectrum502.graph sourceMap0423=true := by decide +kernel
theorem fusedMap0423_checked : acceptsGraphIso
    (fused (graph core0423) (root 6) 0 3) DegreeOneSmallSpectrum505.graph fusedMap0423=true := by decide +kernel
theorem certified0423 : Certified (graph core0423) (root 6) 0 3 :=
  of_native_maps core0423 DegreeOneSmallSpectrum502.graph DegreeOneSmallSpectrum505.graph
    sourceMap0423 fusedMap0423 sourceMap0423_checked fusedMap0423_checked
    DegreeOneSmallComparisons.comparison0423
#print axioms sourceMap0423_checked
#print axioms fusedMap0423_checked
#print axioms certified0423
def sourceMap0423swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,7] (sourceLabel 6 3 0 v)
def fusedMap0423swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0423swap_checked : acceptsGraphIso
    (source (graph core0423) (root 6) 3 0) DegreeOneSmallSpectrum502.graph sourceMap0423swap=true := by decide +kernel
theorem fusedMap0423swap_checked : acceptsGraphIso
    (fused (graph core0423) (root 6) 3 0) DegreeOneSmallSpectrum505.graph fusedMap0423swap=true := by decide +kernel
theorem certified0423swap : Certified (graph core0423) (root 6) 3 0 :=
  of_native_maps core0423 DegreeOneSmallSpectrum502.graph DegreeOneSmallSpectrum505.graph
    sourceMap0423swap fusedMap0423swap sourceMap0423swap_checked fusedMap0423swap_checked
    DegreeOneSmallComparisons.comparison0423
#print axioms sourceMap0423swap_checked
#print axioms fusedMap0423swap_checked
#print axioms certified0423swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
