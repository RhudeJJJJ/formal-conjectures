/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0418 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0418 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 1 3 v)
def fusedMap0418 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0418_checked : acceptsGraphIso
    (source (graph core0418) (root 6) 1 3) DegreeOneSmallSpectrum1119.graph sourceMap0418=true := by decide +kernel
theorem fusedMap0418_checked : acceptsGraphIso
    (fused (graph core0418) (root 6) 1 3) DegreeOneSmallSpectrum872.graph fusedMap0418=true := by decide +kernel
theorem certified0418 : Certified (graph core0418) (root 6) 1 3 :=
  of_native_maps core0418 DegreeOneSmallSpectrum1119.graph DegreeOneSmallSpectrum872.graph
    sourceMap0418 fusedMap0418 sourceMap0418_checked fusedMap0418_checked
    DegreeOneSmallComparisons.comparison0418
#print axioms sourceMap0418_checked
#print axioms fusedMap0418_checked
#print axioms certified0418
def sourceMap0418swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,7,8] (sourceLabel 6 3 1 v)
def fusedMap0418swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0418swap_checked : acceptsGraphIso
    (source (graph core0418) (root 6) 3 1) DegreeOneSmallSpectrum1119.graph sourceMap0418swap=true := by decide +kernel
theorem fusedMap0418swap_checked : acceptsGraphIso
    (fused (graph core0418) (root 6) 3 1) DegreeOneSmallSpectrum872.graph fusedMap0418swap=true := by decide +kernel
theorem certified0418swap : Certified (graph core0418) (root 6) 3 1 :=
  of_native_maps core0418 DegreeOneSmallSpectrum1119.graph DegreeOneSmallSpectrum872.graph
    sourceMap0418swap fusedMap0418swap sourceMap0418swap_checked fusedMap0418swap_checked
    DegreeOneSmallComparisons.comparison0418
#print axioms sourceMap0418swap_checked
#print axioms fusedMap0418swap_checked
#print axioms certified0418swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
