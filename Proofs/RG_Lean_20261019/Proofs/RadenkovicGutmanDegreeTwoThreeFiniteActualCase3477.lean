/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3477 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3477 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (sourceLabel 4 0 6 v)
def fusedMap3477 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 0 6 v)
theorem sourceMap3477_checked : acceptsGraphIso
    (source (graph core3477) (root 4) 0 6) DegreeOneSmallSpectrum956.graph sourceMap3477=true := by decide +kernel
theorem fusedMap3477_checked : acceptsGraphIso
    (fused (graph core3477) (root 4) 0 6) DegreeOneSmallSpectrum858.graph fusedMap3477=true := by decide +kernel
theorem certified3477 : Certified (graph core3477) (root 4) 0 6 :=
  of_native_maps core3477 DegreeOneSmallSpectrum956.graph DegreeOneSmallSpectrum858.graph
    sourceMap3477 fusedMap3477 sourceMap3477_checked fusedMap3477_checked
    DegreeTwoThreeFiniteComparisons.comparison3477
#print axioms sourceMap3477_checked
#print axioms fusedMap3477_checked
#print axioms certified3477
def sourceMap3477swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,12,7] (sourceLabel 4 6 0 v)
def fusedMap3477swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 6 0 v)
theorem sourceMap3477swap_checked : acceptsGraphIso
    (source (graph core3477) (root 4) 6 0) DegreeOneSmallSpectrum956.graph sourceMap3477swap=true := by decide +kernel
theorem fusedMap3477swap_checked : acceptsGraphIso
    (fused (graph core3477) (root 4) 6 0) DegreeOneSmallSpectrum858.graph fusedMap3477swap=true := by decide +kernel
theorem certified3477swap : Certified (graph core3477) (root 4) 6 0 :=
  of_native_maps core3477 DegreeOneSmallSpectrum956.graph DegreeOneSmallSpectrum858.graph
    sourceMap3477swap fusedMap3477swap sourceMap3477swap_checked fusedMap3477swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3477
#print axioms sourceMap3477swap_checked
#print axioms fusedMap3477swap_checked
#print axioms certified3477swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
