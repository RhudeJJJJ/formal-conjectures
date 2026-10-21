/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0404 : Family 6 := level6.get ⟨22,by decide⟩
def sourceMap0404 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0404 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0404_checked : acceptsGraphIso
    (source (graph core0404) (root 6) 0 2) DegreeOneSmallSpectrum281.graph sourceMap0404=true := by decide +kernel
theorem fusedMap0404_checked : acceptsGraphIso
    (fused (graph core0404) (root 6) 0 2) DegreeOneSmallSpectrum176.graph fusedMap0404=true := by decide +kernel
theorem certified0404 : Certified (graph core0404) (root 6) 0 2 :=
  of_native_maps core0404 DegreeOneSmallSpectrum281.graph DegreeOneSmallSpectrum176.graph
    sourceMap0404 fusedMap0404 sourceMap0404_checked fusedMap0404_checked
    DegreeOneSmallComparisons.comparison0404
#print axioms sourceMap0404_checked
#print axioms fusedMap0404_checked
#print axioms certified0404
def sourceMap0404swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0404swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0404swap_checked : acceptsGraphIso
    (source (graph core0404) (root 6) 2 0) DegreeOneSmallSpectrum281.graph sourceMap0404swap=true := by decide +kernel
theorem fusedMap0404swap_checked : acceptsGraphIso
    (fused (graph core0404) (root 6) 2 0) DegreeOneSmallSpectrum176.graph fusedMap0404swap=true := by decide +kernel
theorem certified0404swap : Certified (graph core0404) (root 6) 2 0 :=
  of_native_maps core0404 DegreeOneSmallSpectrum281.graph DegreeOneSmallSpectrum176.graph
    sourceMap0404swap fusedMap0404swap sourceMap0404swap_checked fusedMap0404swap_checked
    DegreeOneSmallComparisons.comparison0404
#print axioms sourceMap0404swap_checked
#print axioms fusedMap0404swap_checked
#print axioms certified0404swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
