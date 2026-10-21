/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0426 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0426 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0426 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0426_checked : acceptsGraphIso
    (source (graph core0426) (root 6) 1 2) DegreeOneSmallSpectrum786.graph sourceMap0426=true := by decide +kernel
theorem fusedMap0426_checked : acceptsGraphIso
    (fused (graph core0426) (root 6) 1 2) DegreeOneSmallSpectrum505.graph fusedMap0426=true := by decide +kernel
theorem certified0426 : Certified (graph core0426) (root 6) 1 2 :=
  of_native_maps core0426 DegreeOneSmallSpectrum786.graph DegreeOneSmallSpectrum505.graph
    sourceMap0426 fusedMap0426 sourceMap0426_checked fusedMap0426_checked
    DegreeOneSmallComparisons.comparison0426
#print axioms sourceMap0426_checked
#print axioms fusedMap0426_checked
#print axioms certified0426
def sourceMap0426swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0426swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0426swap_checked : acceptsGraphIso
    (source (graph core0426) (root 6) 2 1) DegreeOneSmallSpectrum786.graph sourceMap0426swap=true := by decide +kernel
theorem fusedMap0426swap_checked : acceptsGraphIso
    (fused (graph core0426) (root 6) 2 1) DegreeOneSmallSpectrum505.graph fusedMap0426swap=true := by decide +kernel
theorem certified0426swap : Certified (graph core0426) (root 6) 2 1 :=
  of_native_maps core0426 DegreeOneSmallSpectrum786.graph DegreeOneSmallSpectrum505.graph
    sourceMap0426swap fusedMap0426swap sourceMap0426swap_checked fusedMap0426swap_checked
    DegreeOneSmallComparisons.comparison0426
#print axioms sourceMap0426swap_checked
#print axioms fusedMap0426swap_checked
#print axioms certified0426swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
