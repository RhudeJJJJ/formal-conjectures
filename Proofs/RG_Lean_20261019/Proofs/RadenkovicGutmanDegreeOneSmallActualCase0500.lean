/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0500 : Family 7 := level7.get ⟨9,by decide⟩
def sourceMap0500 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0500 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0500_checked : acceptsGraphIso
    (source (graph core0500) (root 7) 1 2) DegreeOneSmallSpectrum1242.graph sourceMap0500=true := by decide +kernel
theorem fusedMap0500_checked : acceptsGraphIso
    (fused (graph core0500) (root 7) 1 2) DegreeOneSmallSpectrum887.graph fusedMap0500=true := by decide +kernel
theorem certified0500 : Certified (graph core0500) (root 7) 1 2 :=
  of_native_maps core0500 DegreeOneSmallSpectrum1242.graph DegreeOneSmallSpectrum887.graph
    sourceMap0500 fusedMap0500 sourceMap0500_checked fusedMap0500_checked
    DegreeOneSmallComparisons.comparison0500
#print axioms sourceMap0500_checked
#print axioms fusedMap0500_checked
#print axioms certified0500
def sourceMap0500swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0500swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0500swap_checked : acceptsGraphIso
    (source (graph core0500) (root 7) 2 1) DegreeOneSmallSpectrum1242.graph sourceMap0500swap=true := by decide +kernel
theorem fusedMap0500swap_checked : acceptsGraphIso
    (fused (graph core0500) (root 7) 2 1) DegreeOneSmallSpectrum887.graph fusedMap0500swap=true := by decide +kernel
theorem certified0500swap : Certified (graph core0500) (root 7) 2 1 :=
  of_native_maps core0500 DegreeOneSmallSpectrum1242.graph DegreeOneSmallSpectrum887.graph
    sourceMap0500swap fusedMap0500swap sourceMap0500swap_checked fusedMap0500swap_checked
    DegreeOneSmallComparisons.comparison0500
#print axioms sourceMap0500swap_checked
#print axioms fusedMap0500swap_checked
#print axioms certified0500swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
