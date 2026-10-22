/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3081 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap3081 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap3081 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap3081_checked : acceptsGraphIso
    (source (graph core3081) (root 5) 0 5) DegreeOneSmallSpectrum974.graph sourceMap3081=true := by decide +kernel
theorem fusedMap3081_checked : acceptsGraphIso
    (fused (graph core3081) (root 5) 0 5) DegreeOneSmallSpectrum859.graph fusedMap3081=true := by decide +kernel
theorem certified3081 : Certified (graph core3081) (root 5) 0 5 :=
  of_native_maps core3081 DegreeOneSmallSpectrum974.graph DegreeOneSmallSpectrum859.graph
    sourceMap3081 fusedMap3081 sourceMap3081_checked fusedMap3081_checked
    DegreeTwoThreeFiniteComparisons.comparison3081
#print axioms sourceMap3081_checked
#print axioms fusedMap3081_checked
#print axioms certified3081
def sourceMap3081swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap3081swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap3081swap_checked : acceptsGraphIso
    (source (graph core3081) (root 5) 5 0) DegreeOneSmallSpectrum974.graph sourceMap3081swap=true := by decide +kernel
theorem fusedMap3081swap_checked : acceptsGraphIso
    (fused (graph core3081) (root 5) 5 0) DegreeOneSmallSpectrum859.graph fusedMap3081swap=true := by decide +kernel
theorem certified3081swap : Certified (graph core3081) (root 5) 5 0 :=
  of_native_maps core3081 DegreeOneSmallSpectrum974.graph DegreeOneSmallSpectrum859.graph
    sourceMap3081swap fusedMap3081swap sourceMap3081swap_checked fusedMap3081swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3081
#print axioms sourceMap3081swap_checked
#print axioms fusedMap3081swap_checked
#print axioms certified3081swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
