/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1045 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap1045 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,10,6,7,8] (sourceLabel 6 0 2 v)
def fusedMap1045 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9] (fusedLabel 6 0 2 v)
theorem sourceMap1045_checked : acceptsGraphIso
    (source (graph core1045) (root 6) 0 2) DegreeOneSmallSpectrum215.graph sourceMap1045=true := by decide +kernel
theorem fusedMap1045_checked : acceptsGraphIso
    (fused (graph core1045) (root 6) 0 2) DegreeOneSmallSpectrum217.graph fusedMap1045=true := by decide +kernel
theorem certified1045 : Certified (graph core1045) (root 6) 0 2 :=
  of_native_maps core1045 DegreeOneSmallSpectrum215.graph DegreeOneSmallSpectrum217.graph
    sourceMap1045 fusedMap1045 sourceMap1045_checked fusedMap1045_checked
    DegreeTwoThreeFiniteComparisons.comparison1045
#print axioms sourceMap1045_checked
#print axioms fusedMap1045_checked
#print axioms certified1045
def sourceMap1045swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,6,7,8,10] (sourceLabel 6 2 0 v)
def fusedMap1045swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9] (fusedLabel 6 2 0 v)
theorem sourceMap1045swap_checked : acceptsGraphIso
    (source (graph core1045) (root 6) 2 0) DegreeOneSmallSpectrum215.graph sourceMap1045swap=true := by decide +kernel
theorem fusedMap1045swap_checked : acceptsGraphIso
    (fused (graph core1045) (root 6) 2 0) DegreeOneSmallSpectrum217.graph fusedMap1045swap=true := by decide +kernel
theorem certified1045swap : Certified (graph core1045) (root 6) 2 0 :=
  of_native_maps core1045 DegreeOneSmallSpectrum215.graph DegreeOneSmallSpectrum217.graph
    sourceMap1045swap fusedMap1045swap sourceMap1045swap_checked fusedMap1045swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1045
#print axioms sourceMap1045swap_checked
#print axioms fusedMap1045swap_checked
#print axioms certified1045swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
