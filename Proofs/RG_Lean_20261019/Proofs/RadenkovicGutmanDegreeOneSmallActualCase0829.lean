/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0829 : Family 8 := level8.get ⟨27,by decide⟩
def sourceMap0829 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0829 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap0829_checked : acceptsGraphIso
    (source (graph core0829) (root 8) 0 2) DegreeOneSmallSpectrum960.graph sourceMap0829=true := by decide +kernel
theorem fusedMap0829_checked : acceptsGraphIso
    (fused (graph core0829) (root 8) 0 2) DegreeOneSmallSpectrum976.graph fusedMap0829=true := by decide +kernel
theorem certified0829 : Certified (graph core0829) (root 8) 0 2 :=
  of_native_maps core0829 DegreeOneSmallSpectrum960.graph DegreeOneSmallSpectrum976.graph
    sourceMap0829 fusedMap0829 sourceMap0829_checked fusedMap0829_checked
    DegreeOneSmallComparisons.comparison0829
#print axioms sourceMap0829_checked
#print axioms fusedMap0829_checked
#print axioms certified0829
def sourceMap0829swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0829swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap0829swap_checked : acceptsGraphIso
    (source (graph core0829) (root 8) 2 0) DegreeOneSmallSpectrum960.graph sourceMap0829swap=true := by decide +kernel
theorem fusedMap0829swap_checked : acceptsGraphIso
    (fused (graph core0829) (root 8) 2 0) DegreeOneSmallSpectrum976.graph fusedMap0829swap=true := by decide +kernel
theorem certified0829swap : Certified (graph core0829) (root 8) 2 0 :=
  of_native_maps core0829 DegreeOneSmallSpectrum960.graph DegreeOneSmallSpectrum976.graph
    sourceMap0829swap fusedMap0829swap sourceMap0829swap_checked fusedMap0829swap_checked
    DegreeOneSmallComparisons.comparison0829
#print axioms sourceMap0829swap_checked
#print axioms fusedMap0829swap_checked
#print axioms certified0829swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
