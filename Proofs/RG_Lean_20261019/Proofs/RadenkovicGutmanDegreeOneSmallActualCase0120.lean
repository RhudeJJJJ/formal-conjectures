/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0120 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0120 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 1 3 v)
def fusedMap0120 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 1 3 v)
theorem sourceMap0120_checked : acceptsGraphIso
    (source (graph core0120) (root 4) 1 3) DegreeOneSmallSpectrum183.graph sourceMap0120=true := by decide +kernel
theorem fusedMap0120_checked : acceptsGraphIso
    (fused (graph core0120) (root 4) 1 3) DegreeOneSmallSpectrum164.graph fusedMap0120=true := by decide +kernel
theorem certified0120 : Certified (graph core0120) (root 4) 1 3 :=
  of_native_maps core0120 DegreeOneSmallSpectrum183.graph DegreeOneSmallSpectrum164.graph
    sourceMap0120 fusedMap0120 sourceMap0120_checked fusedMap0120_checked
    DegreeOneSmallComparisons.comparison0120
#print axioms sourceMap0120_checked
#print axioms fusedMap0120_checked
#print axioms certified0120
def sourceMap0120swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,7,8,9,10,5,6] (sourceLabel 4 3 1 v)
def fusedMap0120swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 3 1 v)
theorem sourceMap0120swap_checked : acceptsGraphIso
    (source (graph core0120) (root 4) 3 1) DegreeOneSmallSpectrum183.graph sourceMap0120swap=true := by decide +kernel
theorem fusedMap0120swap_checked : acceptsGraphIso
    (fused (graph core0120) (root 4) 3 1) DegreeOneSmallSpectrum164.graph fusedMap0120swap=true := by decide +kernel
theorem certified0120swap : Certified (graph core0120) (root 4) 3 1 :=
  of_native_maps core0120 DegreeOneSmallSpectrum183.graph DegreeOneSmallSpectrum164.graph
    sourceMap0120swap fusedMap0120swap sourceMap0120swap_checked fusedMap0120swap_checked
    DegreeOneSmallComparisons.comparison0120
#print axioms sourceMap0120swap_checked
#print axioms fusedMap0120swap_checked
#print axioms certified0120swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
