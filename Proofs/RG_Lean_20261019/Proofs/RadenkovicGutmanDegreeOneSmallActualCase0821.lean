/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0821 : Family 8 := level8.get ⟨25,by decide⟩
def sourceMap0821 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0821 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0821_checked : acceptsGraphIso
    (source (graph core0821) (root 8) 0 2) DegreeOneSmallSpectrum963.graph sourceMap0821=true := by decide +kernel
theorem fusedMap0821_checked : acceptsGraphIso
    (fused (graph core0821) (root 8) 0 2) DegreeOneSmallSpectrum971.graph fusedMap0821=true := by decide +kernel
theorem certified0821 : Certified (graph core0821) (root 8) 0 2 :=
  of_native_maps core0821 DegreeOneSmallSpectrum963.graph DegreeOneSmallSpectrum971.graph
    sourceMap0821 fusedMap0821 sourceMap0821_checked fusedMap0821_checked
    DegreeOneSmallComparisons.comparison0821
#print axioms sourceMap0821_checked
#print axioms fusedMap0821_checked
#print axioms certified0821
def sourceMap0821swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0821swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0821swap_checked : acceptsGraphIso
    (source (graph core0821) (root 8) 2 0) DegreeOneSmallSpectrum963.graph sourceMap0821swap=true := by decide +kernel
theorem fusedMap0821swap_checked : acceptsGraphIso
    (fused (graph core0821) (root 8) 2 0) DegreeOneSmallSpectrum971.graph fusedMap0821swap=true := by decide +kernel
theorem certified0821swap : Certified (graph core0821) (root 8) 2 0 :=
  of_native_maps core0821 DegreeOneSmallSpectrum963.graph DegreeOneSmallSpectrum971.graph
    sourceMap0821swap fusedMap0821swap sourceMap0821swap_checked fusedMap0821swap_checked
    DegreeOneSmallComparisons.comparison0821
#print axioms sourceMap0821swap_checked
#print axioms fusedMap0821swap_checked
#print axioms certified0821swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
