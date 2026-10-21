/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0569 : Family 7 := level7.get ⟨27,by decide⟩
def sourceMap0569 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0569 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0569_checked : acceptsGraphIso
    (source (graph core0569) (root 7) 0 2) DegreeOneSmallSpectrum410.graph sourceMap0569=true := by decide +kernel
theorem fusedMap0569_checked : acceptsGraphIso
    (fused (graph core0569) (root 7) 0 2) DegreeOneSmallSpectrum411.graph fusedMap0569=true := by decide +kernel
theorem certified0569 : Certified (graph core0569) (root 7) 0 2 :=
  of_native_maps core0569 DegreeOneSmallSpectrum410.graph DegreeOneSmallSpectrum411.graph
    sourceMap0569 fusedMap0569 sourceMap0569_checked fusedMap0569_checked
    DegreeOneSmallComparisons.comparison0569
#print axioms sourceMap0569_checked
#print axioms fusedMap0569_checked
#print axioms certified0569
def sourceMap0569swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0569swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0569swap_checked : acceptsGraphIso
    (source (graph core0569) (root 7) 2 0) DegreeOneSmallSpectrum410.graph sourceMap0569swap=true := by decide +kernel
theorem fusedMap0569swap_checked : acceptsGraphIso
    (fused (graph core0569) (root 7) 2 0) DegreeOneSmallSpectrum411.graph fusedMap0569swap=true := by decide +kernel
theorem certified0569swap : Certified (graph core0569) (root 7) 2 0 :=
  of_native_maps core0569 DegreeOneSmallSpectrum410.graph DegreeOneSmallSpectrum411.graph
    sourceMap0569swap fusedMap0569swap sourceMap0569swap_checked fusedMap0569swap_checked
    DegreeOneSmallComparisons.comparison0569
#print axioms sourceMap0569swap_checked
#print axioms fusedMap0569swap_checked
#print axioms certified0569swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
