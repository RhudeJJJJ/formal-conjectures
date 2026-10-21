/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0682 : Family 7 := level7.get ⟨65,by decide⟩
def sourceMap0682 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0682 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0682_checked : acceptsGraphIso
    (source (graph core0682) (root 7) 0 1) DegreeOneSmallSpectrum248.graph sourceMap0682=true := by decide +kernel
theorem fusedMap0682_checked : acceptsGraphIso
    (fused (graph core0682) (root 7) 0 1) DegreeOneSmallSpectrum249.graph fusedMap0682=true := by decide +kernel
theorem certified0682 : Certified (graph core0682) (root 7) 0 1 :=
  of_native_maps core0682 DegreeOneSmallSpectrum248.graph DegreeOneSmallSpectrum249.graph
    sourceMap0682 fusedMap0682 sourceMap0682_checked fusedMap0682_checked
    DegreeOneSmallComparisons.comparison0682
#print axioms sourceMap0682_checked
#print axioms fusedMap0682_checked
#print axioms certified0682
def sourceMap0682swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0682swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0682swap_checked : acceptsGraphIso
    (source (graph core0682) (root 7) 1 0) DegreeOneSmallSpectrum248.graph sourceMap0682swap=true := by decide +kernel
theorem fusedMap0682swap_checked : acceptsGraphIso
    (fused (graph core0682) (root 7) 1 0) DegreeOneSmallSpectrum249.graph fusedMap0682swap=true := by decide +kernel
theorem certified0682swap : Certified (graph core0682) (root 7) 1 0 :=
  of_native_maps core0682 DegreeOneSmallSpectrum248.graph DegreeOneSmallSpectrum249.graph
    sourceMap0682swap fusedMap0682swap sourceMap0682swap_checked fusedMap0682swap_checked
    DegreeOneSmallComparisons.comparison0682
#print axioms sourceMap0682swap_checked
#print axioms fusedMap0682swap_checked
#print axioms certified0682swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
