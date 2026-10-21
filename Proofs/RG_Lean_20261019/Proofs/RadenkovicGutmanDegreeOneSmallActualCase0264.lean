/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0264 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0264 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap0264 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap0264_checked : acceptsGraphIso
    (source (graph core0264) (root 5) 1 4) DegreeOneSmallSpectrum986.graph sourceMap0264=true := by decide +kernel
theorem fusedMap0264_checked : acceptsGraphIso
    (fused (graph core0264) (root 5) 1 4) DegreeOneSmallSpectrum862.graph fusedMap0264=true := by decide +kernel
theorem certified0264 : Certified (graph core0264) (root 5) 1 4 :=
  of_native_maps core0264 DegreeOneSmallSpectrum986.graph DegreeOneSmallSpectrum862.graph
    sourceMap0264 fusedMap0264 sourceMap0264_checked fusedMap0264_checked
    DegreeOneSmallComparisons.comparison0264
#print axioms sourceMap0264_checked
#print axioms fusedMap0264_checked
#print axioms certified0264
def sourceMap0264swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,9,10,11,12,7,8] (sourceLabel 5 4 1 v)
def fusedMap0264swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap0264swap_checked : acceptsGraphIso
    (source (graph core0264) (root 5) 4 1) DegreeOneSmallSpectrum986.graph sourceMap0264swap=true := by decide +kernel
theorem fusedMap0264swap_checked : acceptsGraphIso
    (fused (graph core0264) (root 5) 4 1) DegreeOneSmallSpectrum862.graph fusedMap0264swap=true := by decide +kernel
theorem certified0264swap : Certified (graph core0264) (root 5) 4 1 :=
  of_native_maps core0264 DegreeOneSmallSpectrum986.graph DegreeOneSmallSpectrum862.graph
    sourceMap0264swap fusedMap0264swap sourceMap0264swap_checked fusedMap0264swap_checked
    DegreeOneSmallComparisons.comparison0264
#print axioms sourceMap0264swap_checked
#print axioms fusedMap0264swap_checked
#print axioms certified0264swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
