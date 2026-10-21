/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0598 : Family 7 := level7.get ⟨34,by decide⟩
def sourceMap0598 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,10,8,6,7] (sourceLabel 7 0 1 v)
def fusedMap0598 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0598_checked : acceptsGraphIso
    (source (graph core0598) (root 7) 0 1) DegreeOneSmallSpectrum310.graph sourceMap0598=true := by decide +kernel
theorem fusedMap0598_checked : acceptsGraphIso
    (fused (graph core0598) (root 7) 0 1) DegreeOneSmallSpectrum183.graph fusedMap0598=true := by decide +kernel
theorem certified0598 : Certified (graph core0598) (root 7) 0 1 :=
  of_native_maps core0598 DegreeOneSmallSpectrum310.graph DegreeOneSmallSpectrum183.graph
    sourceMap0598 fusedMap0598 sourceMap0598_checked fusedMap0598_checked
    DegreeOneSmallComparisons.comparison0598
#print axioms sourceMap0598_checked
#print axioms fusedMap0598_checked
#print axioms certified0598
def sourceMap0598swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,10,6,7,8] (sourceLabel 7 1 0 v)
def fusedMap0598swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0598swap_checked : acceptsGraphIso
    (source (graph core0598) (root 7) 1 0) DegreeOneSmallSpectrum310.graph sourceMap0598swap=true := by decide +kernel
theorem fusedMap0598swap_checked : acceptsGraphIso
    (fused (graph core0598) (root 7) 1 0) DegreeOneSmallSpectrum183.graph fusedMap0598swap=true := by decide +kernel
theorem certified0598swap : Certified (graph core0598) (root 7) 1 0 :=
  of_native_maps core0598 DegreeOneSmallSpectrum310.graph DegreeOneSmallSpectrum183.graph
    sourceMap0598swap fusedMap0598swap sourceMap0598swap_checked fusedMap0598swap_checked
    DegreeOneSmallComparisons.comparison0598
#print axioms sourceMap0598swap_checked
#print axioms fusedMap0598swap_checked
#print axioms certified0598swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
