/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0554 : Family 7 := level7.get ⟨21,by decide⟩
def sourceMap0554 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 7 1 2 v)
def fusedMap0554 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0554_checked : acceptsGraphIso
    (source (graph core0554) (root 7) 1 2) DegreeOneSmallSpectrum1490.graph sourceMap0554=true := by decide +kernel
theorem fusedMap0554_checked : acceptsGraphIso
    (fused (graph core0554) (root 7) 1 2) DegreeOneSmallSpectrum971.graph fusedMap0554=true := by decide +kernel
theorem certified0554 : Certified (graph core0554) (root 7) 1 2 :=
  of_native_maps core0554 DegreeOneSmallSpectrum1490.graph DegreeOneSmallSpectrum971.graph
    sourceMap0554 fusedMap0554 sourceMap0554_checked fusedMap0554_checked
    DegreeOneSmallComparisons.comparison0554
#print axioms sourceMap0554_checked
#print axioms fusedMap0554_checked
#print axioms certified0554
def sourceMap0554swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 2 1 v)
def fusedMap0554swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0554swap_checked : acceptsGraphIso
    (source (graph core0554) (root 7) 2 1) DegreeOneSmallSpectrum1490.graph sourceMap0554swap=true := by decide +kernel
theorem fusedMap0554swap_checked : acceptsGraphIso
    (fused (graph core0554) (root 7) 2 1) DegreeOneSmallSpectrum971.graph fusedMap0554swap=true := by decide +kernel
theorem certified0554swap : Certified (graph core0554) (root 7) 2 1 :=
  of_native_maps core0554 DegreeOneSmallSpectrum1490.graph DegreeOneSmallSpectrum971.graph
    sourceMap0554swap fusedMap0554swap sourceMap0554swap_checked fusedMap0554swap_checked
    DegreeOneSmallComparisons.comparison0554
#print axioms sourceMap0554swap_checked
#print axioms fusedMap0554swap_checked
#print axioms certified0554swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
