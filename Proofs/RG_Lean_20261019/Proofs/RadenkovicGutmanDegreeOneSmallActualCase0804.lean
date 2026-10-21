/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0804 : Family 8 := level8.get ⟨20,by decide⟩
def sourceMap0804 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0804 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0804_checked : acceptsGraphIso
    (source (graph core0804) (root 8) 0 1) DegreeOneSmallSpectrum555.graph sourceMap0804=true := by decide +kernel
theorem fusedMap0804_checked : acceptsGraphIso
    (fused (graph core0804) (root 8) 0 1) DegreeOneSmallSpectrum387.graph fusedMap0804=true := by decide +kernel
theorem certified0804 : Certified (graph core0804) (root 8) 0 1 :=
  of_native_maps core0804 DegreeOneSmallSpectrum555.graph DegreeOneSmallSpectrum387.graph
    sourceMap0804 fusedMap0804 sourceMap0804_checked fusedMap0804_checked
    DegreeOneSmallComparisons.comparison0804
#print axioms sourceMap0804_checked
#print axioms fusedMap0804_checked
#print axioms certified0804
def sourceMap0804swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0804swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0804swap_checked : acceptsGraphIso
    (source (graph core0804) (root 8) 1 0) DegreeOneSmallSpectrum555.graph sourceMap0804swap=true := by decide +kernel
theorem fusedMap0804swap_checked : acceptsGraphIso
    (fused (graph core0804) (root 8) 1 0) DegreeOneSmallSpectrum387.graph fusedMap0804swap=true := by decide +kernel
theorem certified0804swap : Certified (graph core0804) (root 8) 1 0 :=
  of_native_maps core0804 DegreeOneSmallSpectrum555.graph DegreeOneSmallSpectrum387.graph
    sourceMap0804swap fusedMap0804swap sourceMap0804swap_checked fusedMap0804swap_checked
    DegreeOneSmallComparisons.comparison0804
#print axioms sourceMap0804swap_checked
#print axioms fusedMap0804swap_checked
#print axioms certified0804swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
