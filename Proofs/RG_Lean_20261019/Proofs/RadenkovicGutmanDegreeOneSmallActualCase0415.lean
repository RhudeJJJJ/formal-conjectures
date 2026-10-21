/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0415 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0415 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0415 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0415_checked : acceptsGraphIso
    (source (graph core0415) (root 6) 0 4) DegreeOneSmallSpectrum1124.graph sourceMap0415=true := by decide +kernel
theorem fusedMap0415_checked : acceptsGraphIso
    (fused (graph core0415) (root 6) 0 4) DegreeOneSmallSpectrum872.graph fusedMap0415=true := by decide +kernel
theorem certified0415 : Certified (graph core0415) (root 6) 0 4 :=
  of_native_maps core0415 DegreeOneSmallSpectrum1124.graph DegreeOneSmallSpectrum872.graph
    sourceMap0415 fusedMap0415 sourceMap0415_checked fusedMap0415_checked
    DegreeOneSmallComparisons.comparison0415
#print axioms sourceMap0415_checked
#print axioms fusedMap0415_checked
#print axioms certified0415
def sourceMap0415swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap0415swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0415swap_checked : acceptsGraphIso
    (source (graph core0415) (root 6) 4 0) DegreeOneSmallSpectrum1124.graph sourceMap0415swap=true := by decide +kernel
theorem fusedMap0415swap_checked : acceptsGraphIso
    (fused (graph core0415) (root 6) 4 0) DegreeOneSmallSpectrum872.graph fusedMap0415swap=true := by decide +kernel
theorem certified0415swap : Certified (graph core0415) (root 6) 4 0 :=
  of_native_maps core0415 DegreeOneSmallSpectrum1124.graph DegreeOneSmallSpectrum872.graph
    sourceMap0415swap fusedMap0415swap sourceMap0415swap_checked fusedMap0415swap_checked
    DegreeOneSmallComparisons.comparison0415
#print axioms sourceMap0415swap_checked
#print axioms fusedMap0415swap_checked
#print axioms certified0415swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
