/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0801 : Family 8 := level8.get ⟨18,by decide⟩
def sourceMap0801 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,11,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap0801 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap0801_checked : acceptsGraphIso
    (source (graph core0801) (root 8) 0 2) DegreeOneSmallSpectrum939.graph sourceMap0801=true := by decide +kernel
theorem fusedMap0801_checked : acceptsGraphIso
    (fused (graph core0801) (root 8) 0 2) DegreeOneSmallSpectrum944.graph fusedMap0801=true := by decide +kernel
theorem certified0801 : Certified (graph core0801) (root 8) 0 2 :=
  of_native_maps core0801 DegreeOneSmallSpectrum939.graph DegreeOneSmallSpectrum944.graph
    sourceMap0801 fusedMap0801 sourceMap0801_checked fusedMap0801_checked
    DegreeOneSmallComparisons.comparison0801
#print axioms sourceMap0801_checked
#print axioms fusedMap0801_checked
#print axioms certified0801
def sourceMap0801swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 8 2 0 v)
def fusedMap0801swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap0801swap_checked : acceptsGraphIso
    (source (graph core0801) (root 8) 2 0) DegreeOneSmallSpectrum939.graph sourceMap0801swap=true := by decide +kernel
theorem fusedMap0801swap_checked : acceptsGraphIso
    (fused (graph core0801) (root 8) 2 0) DegreeOneSmallSpectrum944.graph fusedMap0801swap=true := by decide +kernel
theorem certified0801swap : Certified (graph core0801) (root 8) 2 0 :=
  of_native_maps core0801 DegreeOneSmallSpectrum939.graph DegreeOneSmallSpectrum944.graph
    sourceMap0801swap fusedMap0801swap sourceMap0801swap_checked fusedMap0801swap_checked
    DegreeOneSmallComparisons.comparison0801
#print axioms sourceMap0801swap_checked
#print axioms fusedMap0801swap_checked
#print axioms certified0801swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
