/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0674 : Family 7 := level7.get ⟨62,by decide⟩
def sourceMap0674 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0674 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0674_checked : acceptsGraphIso
    (source (graph core0674) (root 7) 1 2) DegreeOneSmallSpectrum1552.graph sourceMap0674=true := by decide +kernel
theorem fusedMap0674_checked : acceptsGraphIso
    (fused (graph core0674) (root 7) 1 2) DegreeOneSmallSpectrum985.graph fusedMap0674=true := by decide +kernel
theorem certified0674 : Certified (graph core0674) (root 7) 1 2 :=
  of_native_maps core0674 DegreeOneSmallSpectrum1552.graph DegreeOneSmallSpectrum985.graph
    sourceMap0674 fusedMap0674 sourceMap0674_checked fusedMap0674_checked
    DegreeOneSmallComparisons.comparison0674
#print axioms sourceMap0674_checked
#print axioms fusedMap0674_checked
#print axioms certified0674
def sourceMap0674swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0674swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0674swap_checked : acceptsGraphIso
    (source (graph core0674) (root 7) 2 1) DegreeOneSmallSpectrum1552.graph sourceMap0674swap=true := by decide +kernel
theorem fusedMap0674swap_checked : acceptsGraphIso
    (fused (graph core0674) (root 7) 2 1) DegreeOneSmallSpectrum985.graph fusedMap0674swap=true := by decide +kernel
theorem certified0674swap : Certified (graph core0674) (root 7) 2 1 :=
  of_native_maps core0674 DegreeOneSmallSpectrum1552.graph DegreeOneSmallSpectrum985.graph
    sourceMap0674swap fusedMap0674swap sourceMap0674swap_checked fusedMap0674swap_checked
    DegreeOneSmallComparisons.comparison0674
#print axioms sourceMap0674swap_checked
#print axioms fusedMap0674swap_checked
#print axioms certified0674swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
