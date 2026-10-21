/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0713 : Family 7 := level7.get ⟨81,by decide⟩
def sourceMap0713 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0713 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0713_checked : acceptsGraphIso
    (source (graph core0713) (root 7) 0 2) DegreeOneSmallSpectrum777.graph sourceMap0713=true := by decide +kernel
theorem fusedMap0713_checked : acceptsGraphIso
    (fused (graph core0713) (root 7) 0 2) DegreeOneSmallSpectrum500.graph fusedMap0713=true := by decide +kernel
theorem certified0713 : Certified (graph core0713) (root 7) 0 2 :=
  of_native_maps core0713 DegreeOneSmallSpectrum777.graph DegreeOneSmallSpectrum500.graph
    sourceMap0713 fusedMap0713 sourceMap0713_checked fusedMap0713_checked
    DegreeOneSmallComparisons.comparison0713
#print axioms sourceMap0713_checked
#print axioms fusedMap0713_checked
#print axioms certified0713
def sourceMap0713swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0713swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0713swap_checked : acceptsGraphIso
    (source (graph core0713) (root 7) 2 0) DegreeOneSmallSpectrum777.graph sourceMap0713swap=true := by decide +kernel
theorem fusedMap0713swap_checked : acceptsGraphIso
    (fused (graph core0713) (root 7) 2 0) DegreeOneSmallSpectrum500.graph fusedMap0713swap=true := by decide +kernel
theorem certified0713swap : Certified (graph core0713) (root 7) 2 0 :=
  of_native_maps core0713 DegreeOneSmallSpectrum777.graph DegreeOneSmallSpectrum500.graph
    sourceMap0713swap fusedMap0713swap sourceMap0713swap_checked fusedMap0713swap_checked
    DegreeOneSmallComparisons.comparison0713
#print axioms sourceMap0713swap_checked
#print axioms fusedMap0713swap_checked
#print axioms certified0713swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
