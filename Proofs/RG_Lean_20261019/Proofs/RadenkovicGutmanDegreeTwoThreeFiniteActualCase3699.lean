/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3699 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3699 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 9) → Fin 13 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12] (sourceLabel 2 0 8 v)
def fusedMap3699 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 0 8 v)
theorem sourceMap3699_checked : acceptsGraphIso
    (source (graph core3699) (root 2) 0 8) DegreeOneSmallSpectrum870.graph sourceMap3699=true := by decide +kernel
theorem fusedMap3699_checked : acceptsGraphIso
    (fused (graph core3699) (root 2) 0 8) DegreeOneSmallSpectrum856.graph fusedMap3699=true := by decide +kernel
theorem certified3699 : Certified (graph core3699) (root 2) 0 8 :=
  of_native_maps core3699 DegreeOneSmallSpectrum870.graph DegreeOneSmallSpectrum856.graph
    sourceMap3699 fusedMap3699 sourceMap3699_checked fusedMap3699_checked
    DegreeTwoThreeFiniteComparisons.comparison3699
#print axioms sourceMap3699_checked
#print axioms fusedMap3699_checked
#print axioms certified3699
def sourceMap3699swap : (Vertices 2 ⊕ Fin 9 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,8,9,10,11,12,7] (sourceLabel 2 8 0 v)
def fusedMap3699swap : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 8 0 v)
theorem sourceMap3699swap_checked : acceptsGraphIso
    (source (graph core3699) (root 2) 8 0) DegreeOneSmallSpectrum870.graph sourceMap3699swap=true := by decide +kernel
theorem fusedMap3699swap_checked : acceptsGraphIso
    (fused (graph core3699) (root 2) 8 0) DegreeOneSmallSpectrum856.graph fusedMap3699swap=true := by decide +kernel
theorem certified3699swap : Certified (graph core3699) (root 2) 8 0 :=
  of_native_maps core3699 DegreeOneSmallSpectrum870.graph DegreeOneSmallSpectrum856.graph
    sourceMap3699swap fusedMap3699swap sourceMap3699swap_checked fusedMap3699swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3699
#print axioms sourceMap3699swap_checked
#print axioms fusedMap3699swap_checked
#print axioms certified3699swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
