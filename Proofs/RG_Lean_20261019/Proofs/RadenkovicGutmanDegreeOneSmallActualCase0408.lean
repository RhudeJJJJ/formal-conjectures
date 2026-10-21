/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0408 : Family 6 := level6.get ⟨22,by decide⟩
def sourceMap0408 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0408 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0408_checked : acceptsGraphIso
    (source (graph core0408) (root 6) 1 2) DegreeOneSmallSpectrum707.graph sourceMap0408=true := by decide +kernel
theorem fusedMap0408_checked : acceptsGraphIso
    (fused (graph core0408) (root 6) 1 2) DegreeOneSmallSpectrum434.graph fusedMap0408=true := by decide +kernel
theorem certified0408 : Certified (graph core0408) (root 6) 1 2 :=
  of_native_maps core0408 DegreeOneSmallSpectrum707.graph DegreeOneSmallSpectrum434.graph
    sourceMap0408 fusedMap0408 sourceMap0408_checked fusedMap0408_checked
    DegreeOneSmallComparisons.comparison0408
#print axioms sourceMap0408_checked
#print axioms fusedMap0408_checked
#print axioms certified0408
def sourceMap0408swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0408swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0408swap_checked : acceptsGraphIso
    (source (graph core0408) (root 6) 2 1) DegreeOneSmallSpectrum707.graph sourceMap0408swap=true := by decide +kernel
theorem fusedMap0408swap_checked : acceptsGraphIso
    (fused (graph core0408) (root 6) 2 1) DegreeOneSmallSpectrum434.graph fusedMap0408swap=true := by decide +kernel
theorem certified0408swap : Certified (graph core0408) (root 6) 2 1 :=
  of_native_maps core0408 DegreeOneSmallSpectrum707.graph DegreeOneSmallSpectrum434.graph
    sourceMap0408swap fusedMap0408swap sourceMap0408swap_checked fusedMap0408swap_checked
    DegreeOneSmallComparisons.comparison0408
#print axioms sourceMap0408swap_checked
#print axioms fusedMap0408swap_checked
#print axioms certified0408swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
