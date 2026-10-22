/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3083 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap3083 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap3083 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap3083_checked : acceptsGraphIso
    (source (graph core3083) (root 5) 0 5) DegreeOneSmallSpectrum924.graph sourceMap3083=true := by decide +kernel
theorem fusedMap3083_checked : acceptsGraphIso
    (fused (graph core3083) (root 5) 0 5) DegreeOneSmallSpectrum929.graph fusedMap3083=true := by decide +kernel
theorem certified3083 : Certified (graph core3083) (root 5) 0 5 :=
  of_native_maps core3083 DegreeOneSmallSpectrum924.graph DegreeOneSmallSpectrum929.graph
    sourceMap3083 fusedMap3083 sourceMap3083_checked fusedMap3083_checked
    DegreeTwoThreeFiniteComparisons.comparison3083
#print axioms sourceMap3083_checked
#print axioms fusedMap3083_checked
#print axioms certified3083
def sourceMap3083swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap3083swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap3083swap_checked : acceptsGraphIso
    (source (graph core3083) (root 5) 5 0) DegreeOneSmallSpectrum924.graph sourceMap3083swap=true := by decide +kernel
theorem fusedMap3083swap_checked : acceptsGraphIso
    (fused (graph core3083) (root 5) 5 0) DegreeOneSmallSpectrum929.graph fusedMap3083swap=true := by decide +kernel
theorem certified3083swap : Certified (graph core3083) (root 5) 5 0 :=
  of_native_maps core3083 DegreeOneSmallSpectrum924.graph DegreeOneSmallSpectrum929.graph
    sourceMap3083swap fusedMap3083swap sourceMap3083swap_checked fusedMap3083swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3083
#print axioms sourceMap3083swap_checked
#print axioms fusedMap3083swap_checked
#print axioms certified3083swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
