/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0170 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0170 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,5,6,7,1,2,3,4] (sourceLabel 5 2 3 v)
def fusedMap0170 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 2 3 v)
theorem sourceMap0170_checked : acceptsGraphIso
    (source (graph core0170) (root 5) 2 3) DegreeOneSmallSpectrum967.graph sourceMap0170=true := by decide +kernel
theorem fusedMap0170_checked : acceptsGraphIso
    (fused (graph core0170) (root 5) 2 3) DegreeOneSmallSpectrum861.graph fusedMap0170=true := by decide +kernel
theorem certified0170 : Certified (graph core0170) (root 5) 2 3 :=
  of_native_maps core0170 DegreeOneSmallSpectrum967.graph DegreeOneSmallSpectrum861.graph
    sourceMap0170 fusedMap0170 sourceMap0170_checked fusedMap0170_checked
    DegreeOneSmallComparisons.comparison0170
#print axioms sourceMap0170_checked
#print axioms fusedMap0170_checked
#print axioms certified0170
def sourceMap0170swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 5 3 2 v)
def fusedMap0170swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 3 2 v)
theorem sourceMap0170swap_checked : acceptsGraphIso
    (source (graph core0170) (root 5) 3 2) DegreeOneSmallSpectrum967.graph sourceMap0170swap=true := by decide +kernel
theorem fusedMap0170swap_checked : acceptsGraphIso
    (fused (graph core0170) (root 5) 3 2) DegreeOneSmallSpectrum861.graph fusedMap0170swap=true := by decide +kernel
theorem certified0170swap : Certified (graph core0170) (root 5) 3 2 :=
  of_native_maps core0170 DegreeOneSmallSpectrum967.graph DegreeOneSmallSpectrum861.graph
    sourceMap0170swap fusedMap0170swap sourceMap0170swap_checked fusedMap0170swap_checked
    DegreeOneSmallComparisons.comparison0170
#print axioms sourceMap0170swap_checked
#print axioms fusedMap0170swap_checked
#print axioms certified0170swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
