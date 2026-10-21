/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0692 : Family 7 := level7.get ⟨66,by decide⟩
def sourceMap0692 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0692 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0692_checked : acceptsGraphIso
    (source (graph core0692) (root 7) 1 2) DegreeOneSmallSpectrum1653.graph sourceMap0692=true := by decide +kernel
theorem fusedMap0692_checked : acceptsGraphIso
    (fused (graph core0692) (root 7) 1 2) DegreeOneSmallSpectrum1021.graph fusedMap0692=true := by decide +kernel
theorem certified0692 : Certified (graph core0692) (root 7) 1 2 :=
  of_native_maps core0692 DegreeOneSmallSpectrum1653.graph DegreeOneSmallSpectrum1021.graph
    sourceMap0692 fusedMap0692 sourceMap0692_checked fusedMap0692_checked
    DegreeOneSmallComparisons.comparison0692
#print axioms sourceMap0692_checked
#print axioms fusedMap0692_checked
#print axioms certified0692
def sourceMap0692swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0692swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0692swap_checked : acceptsGraphIso
    (source (graph core0692) (root 7) 2 1) DegreeOneSmallSpectrum1653.graph sourceMap0692swap=true := by decide +kernel
theorem fusedMap0692swap_checked : acceptsGraphIso
    (fused (graph core0692) (root 7) 2 1) DegreeOneSmallSpectrum1021.graph fusedMap0692swap=true := by decide +kernel
theorem certified0692swap : Certified (graph core0692) (root 7) 2 1 :=
  of_native_maps core0692 DegreeOneSmallSpectrum1653.graph DegreeOneSmallSpectrum1021.graph
    sourceMap0692swap fusedMap0692swap sourceMap0692swap_checked fusedMap0692swap_checked
    DegreeOneSmallComparisons.comparison0692
#print axioms sourceMap0692swap_checked
#print axioms fusedMap0692swap_checked
#print axioms certified0692swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
