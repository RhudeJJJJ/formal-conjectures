/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0223 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0223 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap0223 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap0223_checked : acceptsGraphIso
    (source (graph core0223) (root 5) 0 4) DegreeOneSmallSpectrum446.graph sourceMap0223=true := by decide +kernel
theorem fusedMap0223_checked : acceptsGraphIso
    (fused (graph core0223) (root 5) 0 4) DegreeOneSmallSpectrum371.graph fusedMap0223=true := by decide +kernel
theorem certified0223 : Certified (graph core0223) (root 5) 0 4 :=
  of_native_maps core0223 DegreeOneSmallSpectrum446.graph DegreeOneSmallSpectrum371.graph
    sourceMap0223 fusedMap0223 sourceMap0223_checked fusedMap0223_checked
    DegreeOneSmallComparisons.comparison0223
#print axioms sourceMap0223_checked
#print axioms fusedMap0223_checked
#print axioms certified0223
def sourceMap0223swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap0223swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap0223swap_checked : acceptsGraphIso
    (source (graph core0223) (root 5) 4 0) DegreeOneSmallSpectrum446.graph sourceMap0223swap=true := by decide +kernel
theorem fusedMap0223swap_checked : acceptsGraphIso
    (fused (graph core0223) (root 5) 4 0) DegreeOneSmallSpectrum371.graph fusedMap0223swap=true := by decide +kernel
theorem certified0223swap : Certified (graph core0223) (root 5) 4 0 :=
  of_native_maps core0223 DegreeOneSmallSpectrum446.graph DegreeOneSmallSpectrum371.graph
    sourceMap0223swap fusedMap0223swap sourceMap0223swap_checked fusedMap0223swap_checked
    DegreeOneSmallComparisons.comparison0223
#print axioms sourceMap0223swap_checked
#print axioms fusedMap0223swap_checked
#print axioms certified0223swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
