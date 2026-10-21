/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0672 : Family 7 := level7.get ⟨62,by decide⟩
def sourceMap0672 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0672 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0672_checked : acceptsGraphIso
    (source (graph core0672) (root 7) 0 3) DegreeOneSmallSpectrum981.graph sourceMap0672=true := by decide +kernel
theorem fusedMap0672_checked : acceptsGraphIso
    (fused (graph core0672) (root 7) 0 3) DegreeOneSmallSpectrum985.graph fusedMap0672=true := by decide +kernel
theorem certified0672 : Certified (graph core0672) (root 7) 0 3 :=
  of_native_maps core0672 DegreeOneSmallSpectrum981.graph DegreeOneSmallSpectrum985.graph
    sourceMap0672 fusedMap0672 sourceMap0672_checked fusedMap0672_checked
    DegreeOneSmallComparisons.comparison0672
#print axioms sourceMap0672_checked
#print axioms fusedMap0672_checked
#print axioms certified0672
def sourceMap0672swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0672swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0672swap_checked : acceptsGraphIso
    (source (graph core0672) (root 7) 3 0) DegreeOneSmallSpectrum981.graph sourceMap0672swap=true := by decide +kernel
theorem fusedMap0672swap_checked : acceptsGraphIso
    (fused (graph core0672) (root 7) 3 0) DegreeOneSmallSpectrum985.graph fusedMap0672swap=true := by decide +kernel
theorem certified0672swap : Certified (graph core0672) (root 7) 3 0 :=
  of_native_maps core0672 DegreeOneSmallSpectrum981.graph DegreeOneSmallSpectrum985.graph
    sourceMap0672swap fusedMap0672swap sourceMap0672swap_checked fusedMap0672swap_checked
    DegreeOneSmallComparisons.comparison0672
#print axioms sourceMap0672swap_checked
#print axioms fusedMap0672swap_checked
#print axioms certified0672swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
