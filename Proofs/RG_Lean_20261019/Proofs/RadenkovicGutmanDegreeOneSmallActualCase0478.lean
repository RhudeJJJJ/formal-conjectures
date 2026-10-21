/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0478 : Family 7 := level7.get ⟨5,by decide⟩
def sourceMap0478 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,6,5,3,4] (sourceLabel 7 0 1 v)
def fusedMap0478 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (fusedLabel 7 0 1 v)
theorem sourceMap0478_checked : acceptsGraphIso
    (source (graph core0478) (root 7) 0 1) DegreeOneSmallSpectrum212.graph sourceMap0478=true := by decide +kernel
theorem fusedMap0478_checked : acceptsGraphIso
    (fused (graph core0478) (root 7) 0 1) DegreeOneSmallSpectrum167.graph fusedMap0478=true := by decide +kernel
theorem certified0478 : Certified (graph core0478) (root 7) 0 1 :=
  of_native_maps core0478 DegreeOneSmallSpectrum212.graph DegreeOneSmallSpectrum167.graph
    sourceMap0478 fusedMap0478 sourceMap0478_checked fusedMap0478_checked
    DegreeOneSmallComparisons.comparison0478
#print axioms sourceMap0478_checked
#print axioms fusedMap0478_checked
#print axioms certified0478
def sourceMap0478swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,6,3,4,5] (sourceLabel 7 1 0 v)
def fusedMap0478swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (fusedLabel 7 1 0 v)
theorem sourceMap0478swap_checked : acceptsGraphIso
    (source (graph core0478) (root 7) 1 0) DegreeOneSmallSpectrum212.graph sourceMap0478swap=true := by decide +kernel
theorem fusedMap0478swap_checked : acceptsGraphIso
    (fused (graph core0478) (root 7) 1 0) DegreeOneSmallSpectrum167.graph fusedMap0478swap=true := by decide +kernel
theorem certified0478swap : Certified (graph core0478) (root 7) 1 0 :=
  of_native_maps core0478 DegreeOneSmallSpectrum212.graph DegreeOneSmallSpectrum167.graph
    sourceMap0478swap fusedMap0478swap sourceMap0478swap_checked fusedMap0478swap_checked
    DegreeOneSmallComparisons.comparison0478
#print axioms sourceMap0478swap_checked
#print axioms fusedMap0478swap_checked
#print axioms certified0478swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
