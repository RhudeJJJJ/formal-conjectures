/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0640 : Family 7 := level7.get ⟨46,by decide⟩
def sourceMap0640 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0640 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0640_checked : acceptsGraphIso
    (source (graph core0640) (root 7) 0 1) DegreeOneSmallSpectrum340.graph sourceMap0640=true := by decide +kernel
theorem fusedMap0640_checked : acceptsGraphIso
    (fused (graph core0640) (root 7) 0 1) DegreeOneSmallSpectrum209.graph fusedMap0640=true := by decide +kernel
theorem certified0640 : Certified (graph core0640) (root 7) 0 1 :=
  of_native_maps core0640 DegreeOneSmallSpectrum340.graph DegreeOneSmallSpectrum209.graph
    sourceMap0640 fusedMap0640 sourceMap0640_checked fusedMap0640_checked
    DegreeOneSmallComparisons.comparison0640
#print axioms sourceMap0640_checked
#print axioms fusedMap0640_checked
#print axioms certified0640
def sourceMap0640swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0640swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0640swap_checked : acceptsGraphIso
    (source (graph core0640) (root 7) 1 0) DegreeOneSmallSpectrum340.graph sourceMap0640swap=true := by decide +kernel
theorem fusedMap0640swap_checked : acceptsGraphIso
    (fused (graph core0640) (root 7) 1 0) DegreeOneSmallSpectrum209.graph fusedMap0640swap=true := by decide +kernel
theorem certified0640swap : Certified (graph core0640) (root 7) 1 0 :=
  of_native_maps core0640 DegreeOneSmallSpectrum340.graph DegreeOneSmallSpectrum209.graph
    sourceMap0640swap fusedMap0640swap sourceMap0640swap_checked fusedMap0640swap_checked
    DegreeOneSmallComparisons.comparison0640
#print axioms sourceMap0640swap_checked
#print axioms fusedMap0640swap_checked
#print axioms certified0640swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
