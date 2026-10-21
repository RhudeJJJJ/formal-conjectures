/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0422 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0422 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0422 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0422_checked : acceptsGraphIso
    (source (graph core0422) (root 6) 0 2) DegreeOneSmallSpectrum324.graph sourceMap0422=true := by decide +kernel
theorem fusedMap0422_checked : acceptsGraphIso
    (fused (graph core0422) (root 6) 0 2) DegreeOneSmallSpectrum198.graph fusedMap0422=true := by decide +kernel
theorem certified0422 : Certified (graph core0422) (root 6) 0 2 :=
  of_native_maps core0422 DegreeOneSmallSpectrum324.graph DegreeOneSmallSpectrum198.graph
    sourceMap0422 fusedMap0422 sourceMap0422_checked fusedMap0422_checked
    DegreeOneSmallComparisons.comparison0422
#print axioms sourceMap0422_checked
#print axioms fusedMap0422_checked
#print axioms certified0422
def sourceMap0422swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0422swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0422swap_checked : acceptsGraphIso
    (source (graph core0422) (root 6) 2 0) DegreeOneSmallSpectrum324.graph sourceMap0422swap=true := by decide +kernel
theorem fusedMap0422swap_checked : acceptsGraphIso
    (fused (graph core0422) (root 6) 2 0) DegreeOneSmallSpectrum198.graph fusedMap0422swap=true := by decide +kernel
theorem certified0422swap : Certified (graph core0422) (root 6) 2 0 :=
  of_native_maps core0422 DegreeOneSmallSpectrum324.graph DegreeOneSmallSpectrum198.graph
    sourceMap0422swap fusedMap0422swap sourceMap0422swap_checked fusedMap0422swap_checked
    DegreeOneSmallComparisons.comparison0422
#print axioms sourceMap0422swap_checked
#print axioms fusedMap0422swap_checked
#print axioms certified0422swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
