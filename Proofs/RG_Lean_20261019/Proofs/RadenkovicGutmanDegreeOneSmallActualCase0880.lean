/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0880 : Family 8 := level8.get ⟨46,by decide⟩
def sourceMap0880 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap0880 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0880_checked : acceptsGraphIso
    (source (graph core0880) (root 8) 0 1) DegreeOneSmallSpectrum474.graph sourceMap0880=true := by decide +kernel
theorem fusedMap0880_checked : acceptsGraphIso
    (fused (graph core0880) (root 8) 0 1) DegreeOneSmallSpectrum479.graph fusedMap0880=true := by decide +kernel
theorem certified0880 : Certified (graph core0880) (root 8) 0 1 :=
  of_native_maps core0880 DegreeOneSmallSpectrum474.graph DegreeOneSmallSpectrum479.graph
    sourceMap0880 fusedMap0880 sourceMap0880_checked fusedMap0880_checked
    DegreeOneSmallComparisons.comparison0880
#print axioms sourceMap0880_checked
#print axioms fusedMap0880_checked
#print axioms certified0880
def sourceMap0880swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap0880swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0880swap_checked : acceptsGraphIso
    (source (graph core0880) (root 8) 1 0) DegreeOneSmallSpectrum474.graph sourceMap0880swap=true := by decide +kernel
theorem fusedMap0880swap_checked : acceptsGraphIso
    (fused (graph core0880) (root 8) 1 0) DegreeOneSmallSpectrum479.graph fusedMap0880swap=true := by decide +kernel
theorem certified0880swap : Certified (graph core0880) (root 8) 1 0 :=
  of_native_maps core0880 DegreeOneSmallSpectrum474.graph DegreeOneSmallSpectrum479.graph
    sourceMap0880swap fusedMap0880swap sourceMap0880swap_checked fusedMap0880swap_checked
    DegreeOneSmallComparisons.comparison0880
#print axioms sourceMap0880swap_checked
#print axioms fusedMap0880swap_checked
#print axioms certified0880swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
