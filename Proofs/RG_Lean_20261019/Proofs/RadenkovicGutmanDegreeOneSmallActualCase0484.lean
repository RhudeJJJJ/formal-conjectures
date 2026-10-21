/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0484 : Family 7 := level7.get ⟨7,by decide⟩
def sourceMap0484 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0484 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0484_checked : acceptsGraphIso
    (source (graph core0484) (root 7) 0 1) DegreeOneSmallSpectrum173.graph sourceMap0484=true := by decide +kernel
theorem fusedMap0484_checked : acceptsGraphIso
    (fused (graph core0484) (root 7) 0 1) DegreeOneSmallSpectrum175.graph fusedMap0484=true := by decide +kernel
theorem certified0484 : Certified (graph core0484) (root 7) 0 1 :=
  of_native_maps core0484 DegreeOneSmallSpectrum173.graph DegreeOneSmallSpectrum175.graph
    sourceMap0484 fusedMap0484 sourceMap0484_checked fusedMap0484_checked
    DegreeOneSmallComparisons.comparison0484
#print axioms sourceMap0484_checked
#print axioms fusedMap0484_checked
#print axioms certified0484
def sourceMap0484swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0484swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0484swap_checked : acceptsGraphIso
    (source (graph core0484) (root 7) 1 0) DegreeOneSmallSpectrum173.graph sourceMap0484swap=true := by decide +kernel
theorem fusedMap0484swap_checked : acceptsGraphIso
    (fused (graph core0484) (root 7) 1 0) DegreeOneSmallSpectrum175.graph fusedMap0484swap=true := by decide +kernel
theorem certified0484swap : Certified (graph core0484) (root 7) 1 0 :=
  of_native_maps core0484 DegreeOneSmallSpectrum173.graph DegreeOneSmallSpectrum175.graph
    sourceMap0484swap fusedMap0484swap sourceMap0484swap_checked fusedMap0484swap_checked
    DegreeOneSmallComparisons.comparison0484
#print axioms sourceMap0484swap_checked
#print axioms fusedMap0484swap_checked
#print axioms certified0484swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
