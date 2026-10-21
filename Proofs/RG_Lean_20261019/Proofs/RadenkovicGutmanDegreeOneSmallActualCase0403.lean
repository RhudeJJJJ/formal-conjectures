/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0403 : Family 6 := level6.get ⟨22,by decide⟩
def sourceMap0403 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0403 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0403_checked : acceptsGraphIso
    (source (graph core0403) (root 6) 0 1) DegreeOneSmallSpectrum110.graph sourceMap0403=true := by decide +kernel
theorem fusedMap0403_checked : acceptsGraphIso
    (fused (graph core0403) (root 6) 0 1) DegreeOneSmallSpectrum111.graph fusedMap0403=true := by decide +kernel
theorem certified0403 : Certified (graph core0403) (root 6) 0 1 :=
  of_native_maps core0403 DegreeOneSmallSpectrum110.graph DegreeOneSmallSpectrum111.graph
    sourceMap0403 fusedMap0403 sourceMap0403_checked fusedMap0403_checked
    DegreeOneSmallComparisons.comparison0403
#print axioms sourceMap0403_checked
#print axioms fusedMap0403_checked
#print axioms certified0403
def sourceMap0403swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0403swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0403swap_checked : acceptsGraphIso
    (source (graph core0403) (root 6) 1 0) DegreeOneSmallSpectrum110.graph sourceMap0403swap=true := by decide +kernel
theorem fusedMap0403swap_checked : acceptsGraphIso
    (fused (graph core0403) (root 6) 1 0) DegreeOneSmallSpectrum111.graph fusedMap0403swap=true := by decide +kernel
theorem certified0403swap : Certified (graph core0403) (root 6) 1 0 :=
  of_native_maps core0403 DegreeOneSmallSpectrum110.graph DegreeOneSmallSpectrum111.graph
    sourceMap0403swap fusedMap0403swap sourceMap0403swap_checked fusedMap0403swap_checked
    DegreeOneSmallComparisons.comparison0403
#print axioms sourceMap0403swap_checked
#print axioms fusedMap0403swap_checked
#print axioms certified0403swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
