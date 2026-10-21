/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0605 : Family 7 := level7.get ⟨35,by decide⟩
def sourceMap0605 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0605 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0605_checked : acceptsGraphIso
    (source (graph core0605) (root 7) 0 2) DegreeOneSmallSpectrum468.graph sourceMap0605=true := by decide +kernel
theorem fusedMap0605_checked : acceptsGraphIso
    (fused (graph core0605) (root 7) 0 2) DegreeOneSmallSpectrum469.graph fusedMap0605=true := by decide +kernel
theorem certified0605 : Certified (graph core0605) (root 7) 0 2 :=
  of_native_maps core0605 DegreeOneSmallSpectrum468.graph DegreeOneSmallSpectrum469.graph
    sourceMap0605 fusedMap0605 sourceMap0605_checked fusedMap0605_checked
    DegreeOneSmallComparisons.comparison0605
#print axioms sourceMap0605_checked
#print axioms fusedMap0605_checked
#print axioms certified0605
def sourceMap0605swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0605swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0605swap_checked : acceptsGraphIso
    (source (graph core0605) (root 7) 2 0) DegreeOneSmallSpectrum468.graph sourceMap0605swap=true := by decide +kernel
theorem fusedMap0605swap_checked : acceptsGraphIso
    (fused (graph core0605) (root 7) 2 0) DegreeOneSmallSpectrum469.graph fusedMap0605swap=true := by decide +kernel
theorem certified0605swap : Certified (graph core0605) (root 7) 2 0 :=
  of_native_maps core0605 DegreeOneSmallSpectrum468.graph DegreeOneSmallSpectrum469.graph
    sourceMap0605swap fusedMap0605swap sourceMap0605swap_checked fusedMap0605swap_checked
    DegreeOneSmallComparisons.comparison0605
#print axioms sourceMap0605swap_checked
#print axioms fusedMap0605swap_checked
#print axioms certified0605swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
