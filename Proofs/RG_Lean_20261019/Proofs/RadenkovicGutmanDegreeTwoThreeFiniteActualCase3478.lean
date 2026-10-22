/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3478 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3478 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (sourceLabel 4 0 6 v)
def fusedMap3478 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 0 6 v)
theorem sourceMap3478_checked : acceptsGraphIso
    (source (graph core3478) (root 4) 0 6) DegreeOneSmallSpectrum872.graph sourceMap3478=true := by decide +kernel
theorem fusedMap3478_checked : acceptsGraphIso
    (fused (graph core3478) (root 4) 0 6) DegreeOneSmallSpectrum879.graph fusedMap3478=true := by decide +kernel
theorem certified3478 : Certified (graph core3478) (root 4) 0 6 :=
  of_native_maps core3478 DegreeOneSmallSpectrum872.graph DegreeOneSmallSpectrum879.graph
    sourceMap3478 fusedMap3478 sourceMap3478_checked fusedMap3478_checked
    DegreeTwoThreeFiniteComparisons.comparison3478
#print axioms sourceMap3478_checked
#print axioms fusedMap3478_checked
#print axioms certified3478
def sourceMap3478swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,12,7] (sourceLabel 4 6 0 v)
def fusedMap3478swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 6 0 v)
theorem sourceMap3478swap_checked : acceptsGraphIso
    (source (graph core3478) (root 4) 6 0) DegreeOneSmallSpectrum872.graph sourceMap3478swap=true := by decide +kernel
theorem fusedMap3478swap_checked : acceptsGraphIso
    (fused (graph core3478) (root 4) 6 0) DegreeOneSmallSpectrum879.graph fusedMap3478swap=true := by decide +kernel
theorem certified3478swap : Certified (graph core3478) (root 4) 6 0 :=
  of_native_maps core3478 DegreeOneSmallSpectrum872.graph DegreeOneSmallSpectrum879.graph
    sourceMap3478swap fusedMap3478swap sourceMap3478swap_checked fusedMap3478swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3478
#print axioms sourceMap3478swap_checked
#print axioms fusedMap3478swap_checked
#print axioms certified3478swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
