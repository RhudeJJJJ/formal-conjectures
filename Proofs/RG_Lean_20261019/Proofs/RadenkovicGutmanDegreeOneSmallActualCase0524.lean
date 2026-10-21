/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0524 : Family 7 := level7.get ⟨14,by decide⟩
def sourceMap0524 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0524 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0524_checked : acceptsGraphIso
    (source (graph core0524) (root 7) 1 2) DegreeOneSmallSpectrum1430.graph sourceMap0524=true := by decide +kernel
theorem fusedMap0524_checked : acceptsGraphIso
    (fused (graph core0524) (root 7) 1 2) DegreeOneSmallSpectrum929.graph fusedMap0524=true := by decide +kernel
theorem certified0524 : Certified (graph core0524) (root 7) 1 2 :=
  of_native_maps core0524 DegreeOneSmallSpectrum1430.graph DegreeOneSmallSpectrum929.graph
    sourceMap0524 fusedMap0524 sourceMap0524_checked fusedMap0524_checked
    DegreeOneSmallComparisons.comparison0524
#print axioms sourceMap0524_checked
#print axioms fusedMap0524_checked
#print axioms certified0524
def sourceMap0524swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0524swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0524swap_checked : acceptsGraphIso
    (source (graph core0524) (root 7) 2 1) DegreeOneSmallSpectrum1430.graph sourceMap0524swap=true := by decide +kernel
theorem fusedMap0524swap_checked : acceptsGraphIso
    (fused (graph core0524) (root 7) 2 1) DegreeOneSmallSpectrum929.graph fusedMap0524swap=true := by decide +kernel
theorem certified0524swap : Certified (graph core0524) (root 7) 2 1 :=
  of_native_maps core0524 DegreeOneSmallSpectrum1430.graph DegreeOneSmallSpectrum929.graph
    sourceMap0524swap fusedMap0524swap sourceMap0524swap_checked fusedMap0524swap_checked
    DegreeOneSmallComparisons.comparison0524
#print axioms sourceMap0524swap_checked
#print axioms fusedMap0524swap_checked
#print axioms certified0524swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
