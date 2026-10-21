/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0490 : Family 7 := level7.get ⟨8,by decide⟩
def sourceMap0490 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0490 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0490_checked : acceptsGraphIso
    (source (graph core0490) (root 7) 0 1) DegreeOneSmallSpectrum180.graph sourceMap0490=true := by decide +kernel
theorem fusedMap0490_checked : acceptsGraphIso
    (fused (graph core0490) (root 7) 0 1) DegreeOneSmallSpectrum182.graph fusedMap0490=true := by decide +kernel
theorem certified0490 : Certified (graph core0490) (root 7) 0 1 :=
  of_native_maps core0490 DegreeOneSmallSpectrum180.graph DegreeOneSmallSpectrum182.graph
    sourceMap0490 fusedMap0490 sourceMap0490_checked fusedMap0490_checked
    DegreeOneSmallComparisons.comparison0490
#print axioms sourceMap0490_checked
#print axioms fusedMap0490_checked
#print axioms certified0490
def sourceMap0490swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0490swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0490swap_checked : acceptsGraphIso
    (source (graph core0490) (root 7) 1 0) DegreeOneSmallSpectrum180.graph sourceMap0490swap=true := by decide +kernel
theorem fusedMap0490swap_checked : acceptsGraphIso
    (fused (graph core0490) (root 7) 1 0) DegreeOneSmallSpectrum182.graph fusedMap0490swap=true := by decide +kernel
theorem certified0490swap : Certified (graph core0490) (root 7) 1 0 :=
  of_native_maps core0490 DegreeOneSmallSpectrum180.graph DegreeOneSmallSpectrum182.graph
    sourceMap0490swap fusedMap0490swap sourceMap0490swap_checked fusedMap0490swap_checked
    DegreeOneSmallComparisons.comparison0490
#print axioms sourceMap0490swap_checked
#print axioms fusedMap0490swap_checked
#print axioms certified0490swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
