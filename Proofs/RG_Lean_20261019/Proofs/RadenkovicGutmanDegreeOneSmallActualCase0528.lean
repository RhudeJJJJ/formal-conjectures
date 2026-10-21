/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0528 : Family 7 := level7.get ⟨15,by decide⟩
def sourceMap0528 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0528 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0528_checked : acceptsGraphIso
    (source (graph core0528) (root 7) 0 3) DegreeOneSmallSpectrum934.graph sourceMap0528=true := by decide +kernel
theorem fusedMap0528_checked : acceptsGraphIso
    (fused (graph core0528) (root 7) 0 3) DegreeOneSmallSpectrum935.graph fusedMap0528=true := by decide +kernel
theorem certified0528 : Certified (graph core0528) (root 7) 0 3 :=
  of_native_maps core0528 DegreeOneSmallSpectrum934.graph DegreeOneSmallSpectrum935.graph
    sourceMap0528 fusedMap0528 sourceMap0528_checked fusedMap0528_checked
    DegreeOneSmallComparisons.comparison0528
#print axioms sourceMap0528_checked
#print axioms fusedMap0528_checked
#print axioms certified0528
def sourceMap0528swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0528swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0528swap_checked : acceptsGraphIso
    (source (graph core0528) (root 7) 3 0) DegreeOneSmallSpectrum934.graph sourceMap0528swap=true := by decide +kernel
theorem fusedMap0528swap_checked : acceptsGraphIso
    (fused (graph core0528) (root 7) 3 0) DegreeOneSmallSpectrum935.graph fusedMap0528swap=true := by decide +kernel
theorem certified0528swap : Certified (graph core0528) (root 7) 3 0 :=
  of_native_maps core0528 DegreeOneSmallSpectrum934.graph DegreeOneSmallSpectrum935.graph
    sourceMap0528swap fusedMap0528swap sourceMap0528swap_checked fusedMap0528swap_checked
    DegreeOneSmallComparisons.comparison0528
#print axioms sourceMap0528swap_checked
#print axioms fusedMap0528swap_checked
#print axioms certified0528swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
