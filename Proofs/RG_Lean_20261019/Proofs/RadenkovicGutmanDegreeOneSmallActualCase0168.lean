/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0168 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0168 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,11,12,6,7,8,9,10] (sourceLabel 5 1 4 v)
def fusedMap0168 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap0168_checked : acceptsGraphIso
    (source (graph core0168) (root 5) 1 4) DegreeOneSmallSpectrum977.graph sourceMap0168=true := by decide +kernel
theorem fusedMap0168_checked : acceptsGraphIso
    (fused (graph core0168) (root 5) 1 4) DegreeOneSmallSpectrum861.graph fusedMap0168=true := by decide +kernel
theorem certified0168 : Certified (graph core0168) (root 5) 1 4 :=
  of_native_maps core0168 DegreeOneSmallSpectrum977.graph DegreeOneSmallSpectrum861.graph
    sourceMap0168 fusedMap0168 sourceMap0168_checked fusedMap0168_checked
    DegreeOneSmallComparisons.comparison0168
#print axioms sourceMap0168_checked
#print axioms fusedMap0168_checked
#print axioms certified0168
def sourceMap0168swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 4 1 v)
def fusedMap0168swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap0168swap_checked : acceptsGraphIso
    (source (graph core0168) (root 5) 4 1) DegreeOneSmallSpectrum977.graph sourceMap0168swap=true := by decide +kernel
theorem fusedMap0168swap_checked : acceptsGraphIso
    (fused (graph core0168) (root 5) 4 1) DegreeOneSmallSpectrum861.graph fusedMap0168swap=true := by decide +kernel
theorem certified0168swap : Certified (graph core0168) (root 5) 4 1 :=
  of_native_maps core0168 DegreeOneSmallSpectrum977.graph DegreeOneSmallSpectrum861.graph
    sourceMap0168swap fusedMap0168swap sourceMap0168swap_checked fusedMap0168swap_checked
    DegreeOneSmallComparisons.comparison0168
#print axioms sourceMap0168swap_checked
#print axioms fusedMap0168swap_checked
#print axioms certified0168swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
