/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0532 : Family 7 := level7.get ⟨17,by decide⟩
def sourceMap0532 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0532 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0532_checked : acceptsGraphIso
    (source (graph core0532) (root 7) 0 1) DegreeOneSmallSpectrum214.graph sourceMap0532=true := by decide +kernel
theorem fusedMap0532_checked : acceptsGraphIso
    (fused (graph core0532) (root 7) 0 1) DegreeOneSmallSpectrum222.graph fusedMap0532=true := by decide +kernel
theorem certified0532 : Certified (graph core0532) (root 7) 0 1 :=
  of_native_maps core0532 DegreeOneSmallSpectrum214.graph DegreeOneSmallSpectrum222.graph
    sourceMap0532 fusedMap0532 sourceMap0532_checked fusedMap0532_checked
    DegreeOneSmallComparisons.comparison0532
#print axioms sourceMap0532_checked
#print axioms fusedMap0532_checked
#print axioms certified0532
def sourceMap0532swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0532swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0532swap_checked : acceptsGraphIso
    (source (graph core0532) (root 7) 1 0) DegreeOneSmallSpectrum214.graph sourceMap0532swap=true := by decide +kernel
theorem fusedMap0532swap_checked : acceptsGraphIso
    (fused (graph core0532) (root 7) 1 0) DegreeOneSmallSpectrum222.graph fusedMap0532swap=true := by decide +kernel
theorem certified0532swap : Certified (graph core0532) (root 7) 1 0 :=
  of_native_maps core0532 DegreeOneSmallSpectrum214.graph DegreeOneSmallSpectrum222.graph
    sourceMap0532swap fusedMap0532swap sourceMap0532swap_checked fusedMap0532swap_checked
    DegreeOneSmallComparisons.comparison0532
#print axioms sourceMap0532swap_checked
#print axioms fusedMap0532swap_checked
#print axioms certified0532swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
