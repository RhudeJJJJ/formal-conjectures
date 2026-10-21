/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0442 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0442 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0442 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0442_checked : acceptsGraphIso
    (source (graph core0442) (root 6) 0 4) DegreeOneSmallSpectrum980.graph sourceMap0442=true := by decide +kernel
theorem fusedMap0442_checked : acceptsGraphIso
    (fused (graph core0442) (root 6) 0 4) DegreeOneSmallSpectrum985.graph fusedMap0442=true := by decide +kernel
theorem certified0442 : Certified (graph core0442) (root 6) 0 4 :=
  of_native_maps core0442 DegreeOneSmallSpectrum980.graph DegreeOneSmallSpectrum985.graph
    sourceMap0442 fusedMap0442 sourceMap0442_checked fusedMap0442_checked
    DegreeOneSmallComparisons.comparison0442
#print axioms sourceMap0442_checked
#print axioms fusedMap0442_checked
#print axioms certified0442
def sourceMap0442swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap0442swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0442swap_checked : acceptsGraphIso
    (source (graph core0442) (root 6) 4 0) DegreeOneSmallSpectrum980.graph sourceMap0442swap=true := by decide +kernel
theorem fusedMap0442swap_checked : acceptsGraphIso
    (fused (graph core0442) (root 6) 4 0) DegreeOneSmallSpectrum985.graph fusedMap0442swap=true := by decide +kernel
theorem certified0442swap : Certified (graph core0442) (root 6) 4 0 :=
  of_native_maps core0442 DegreeOneSmallSpectrum980.graph DegreeOneSmallSpectrum985.graph
    sourceMap0442swap fusedMap0442swap sourceMap0442swap_checked fusedMap0442swap_checked
    DegreeOneSmallComparisons.comparison0442
#print axioms sourceMap0442swap_checked
#print axioms fusedMap0442swap_checked
#print axioms certified0442swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
