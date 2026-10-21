/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0399 : Family 6 := level6.get ⟨20,by decide⟩
def sourceMap0399 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0399 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0399_checked : acceptsGraphIso
    (source (graph core0399) (root 6) 1 2) DegreeOneSmallSpectrum656.graph sourceMap0399=true := by decide +kernel
theorem fusedMap0399_checked : acceptsGraphIso
    (fused (graph core0399) (root 6) 1 2) DegreeOneSmallSpectrum411.graph fusedMap0399=true := by decide +kernel
theorem certified0399 : Certified (graph core0399) (root 6) 1 2 :=
  of_native_maps core0399 DegreeOneSmallSpectrum656.graph DegreeOneSmallSpectrum411.graph
    sourceMap0399 fusedMap0399 sourceMap0399_checked fusedMap0399_checked
    DegreeOneSmallComparisons.comparison0399
#print axioms sourceMap0399_checked
#print axioms fusedMap0399_checked
#print axioms certified0399
def sourceMap0399swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0399swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0399swap_checked : acceptsGraphIso
    (source (graph core0399) (root 6) 2 1) DegreeOneSmallSpectrum656.graph sourceMap0399swap=true := by decide +kernel
theorem fusedMap0399swap_checked : acceptsGraphIso
    (fused (graph core0399) (root 6) 2 1) DegreeOneSmallSpectrum411.graph fusedMap0399swap=true := by decide +kernel
theorem certified0399swap : Certified (graph core0399) (root 6) 2 1 :=
  of_native_maps core0399 DegreeOneSmallSpectrum656.graph DegreeOneSmallSpectrum411.graph
    sourceMap0399swap fusedMap0399swap sourceMap0399swap_checked fusedMap0399swap_checked
    DegreeOneSmallComparisons.comparison0399
#print axioms sourceMap0399swap_checked
#print axioms fusedMap0399swap_checked
#print axioms certified0399swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
