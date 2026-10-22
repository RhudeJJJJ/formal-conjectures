/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3479 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3479 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (sourceLabel 4 0 6 v)
def fusedMap3479 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 0 6 v)
theorem sourceMap3479_checked : acceptsGraphIso
    (source (graph core3479) (root 4) 0 6) DegreeOneSmallSpectrum909.graph sourceMap3479=true := by decide +kernel
theorem fusedMap3479_checked : acceptsGraphIso
    (fused (graph core3479) (root 4) 0 6) DegreeOneSmallSpectrum915.graph fusedMap3479=true := by decide +kernel
theorem certified3479 : Certified (graph core3479) (root 4) 0 6 :=
  of_native_maps core3479 DegreeOneSmallSpectrum909.graph DegreeOneSmallSpectrum915.graph
    sourceMap3479 fusedMap3479 sourceMap3479_checked fusedMap3479_checked
    DegreeTwoThreeFiniteComparisons.comparison3479
#print axioms sourceMap3479_checked
#print axioms fusedMap3479_checked
#print axioms certified3479
def sourceMap3479swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,12,7] (sourceLabel 4 6 0 v)
def fusedMap3479swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 6 0 v)
theorem sourceMap3479swap_checked : acceptsGraphIso
    (source (graph core3479) (root 4) 6 0) DegreeOneSmallSpectrum909.graph sourceMap3479swap=true := by decide +kernel
theorem fusedMap3479swap_checked : acceptsGraphIso
    (fused (graph core3479) (root 4) 6 0) DegreeOneSmallSpectrum915.graph fusedMap3479swap=true := by decide +kernel
theorem certified3479swap : Certified (graph core3479) (root 4) 6 0 :=
  of_native_maps core3479 DegreeOneSmallSpectrum909.graph DegreeOneSmallSpectrum915.graph
    sourceMap3479swap fusedMap3479swap sourceMap3479swap_checked fusedMap3479swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3479
#print axioms sourceMap3479swap_checked
#print axioms fusedMap3479swap_checked
#print axioms certified3479swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
