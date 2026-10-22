/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3927 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3927 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (sourceLabel 4 1 5 v)
def fusedMap3927 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 1 5 v)
theorem sourceMap3927_checked : acceptsGraphIso
    (source (graph core3927) (root 4) 1 5) DegreeOneSmallSpectrum1296.graph sourceMap3927=true := by decide +kernel
theorem fusedMap3927_checked : acceptsGraphIso
    (fused (graph core3927) (root 4) 1 5) DegreeOneSmallSpectrum915.graph fusedMap3927=true := by decide +kernel
theorem certified3927 : Certified (graph core3927) (root 4) 1 5 :=
  of_native_maps core3927 DegreeOneSmallSpectrum1296.graph DegreeOneSmallSpectrum915.graph
    sourceMap3927 fusedMap3927 sourceMap3927_checked fusedMap3927_checked
    DegreeTwoThreeFiniteComparisons.comparison3927
#print axioms sourceMap3927_checked
#print axioms fusedMap3927_checked
#print axioms certified3927
def sourceMap3927swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,9,10,11,12,7,8] (sourceLabel 4 5 1 v)
def fusedMap3927swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 5 1 v)
theorem sourceMap3927swap_checked : acceptsGraphIso
    (source (graph core3927) (root 4) 5 1) DegreeOneSmallSpectrum1296.graph sourceMap3927swap=true := by decide +kernel
theorem fusedMap3927swap_checked : acceptsGraphIso
    (fused (graph core3927) (root 4) 5 1) DegreeOneSmallSpectrum915.graph fusedMap3927swap=true := by decide +kernel
theorem certified3927swap : Certified (graph core3927) (root 4) 5 1 :=
  of_native_maps core3927 DegreeOneSmallSpectrum1296.graph DegreeOneSmallSpectrum915.graph
    sourceMap3927swap fusedMap3927swap sourceMap3927swap_checked fusedMap3927swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3927
#print axioms sourceMap3927swap_checked
#print axioms fusedMap3927swap_checked
#print axioms certified3927swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
