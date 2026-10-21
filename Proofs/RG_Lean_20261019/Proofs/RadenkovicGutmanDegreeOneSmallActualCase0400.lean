/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0400 : Family 6 := level6.get ⟨20,by decide⟩
def sourceMap0400 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 1 3 v)
def fusedMap0400 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0400_checked : acceptsGraphIso
    (source (graph core0400) (root 6) 1 3) DegreeOneSmallSpectrum1022.graph sourceMap0400=true := by decide +kernel
theorem fusedMap0400_checked : acceptsGraphIso
    (fused (graph core0400) (root 6) 1 3) DegreeOneSmallSpectrum863.graph fusedMap0400=true := by decide +kernel
theorem certified0400 : Certified (graph core0400) (root 6) 1 3 :=
  of_native_maps core0400 DegreeOneSmallSpectrum1022.graph DegreeOneSmallSpectrum863.graph
    sourceMap0400 fusedMap0400 sourceMap0400_checked fusedMap0400_checked
    DegreeOneSmallComparisons.comparison0400
#print axioms sourceMap0400_checked
#print axioms fusedMap0400_checked
#print axioms certified0400
def sourceMap0400swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,7,8] (sourceLabel 6 3 1 v)
def fusedMap0400swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0400swap_checked : acceptsGraphIso
    (source (graph core0400) (root 6) 3 1) DegreeOneSmallSpectrum1022.graph sourceMap0400swap=true := by decide +kernel
theorem fusedMap0400swap_checked : acceptsGraphIso
    (fused (graph core0400) (root 6) 3 1) DegreeOneSmallSpectrum863.graph fusedMap0400swap=true := by decide +kernel
theorem certified0400swap : Certified (graph core0400) (root 6) 3 1 :=
  of_native_maps core0400 DegreeOneSmallSpectrum1022.graph DegreeOneSmallSpectrum863.graph
    sourceMap0400swap fusedMap0400swap sourceMap0400swap_checked fusedMap0400swap_checked
    DegreeOneSmallComparisons.comparison0400
#print axioms sourceMap0400swap_checked
#print axioms fusedMap0400swap_checked
#print axioms certified0400swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
