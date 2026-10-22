/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2068 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap2068 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2068 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2068_checked : acceptsGraphIso
    (source (graph core2068) (root 6) 0 4) DegreeOneSmallSpectrum931.graph sourceMap2068=true := by decide +kernel
theorem fusedMap2068_checked : acceptsGraphIso
    (fused (graph core2068) (root 6) 0 4) DegreeOneSmallSpectrum935.graph fusedMap2068=true := by decide +kernel
theorem certified2068 : Certified (graph core2068) (root 6) 0 4 :=
  of_native_maps core2068 DegreeOneSmallSpectrum931.graph DegreeOneSmallSpectrum935.graph
    sourceMap2068 fusedMap2068 sourceMap2068_checked fusedMap2068_checked
    DegreeTwoThreeFiniteComparisons.comparison2068
#print axioms sourceMap2068_checked
#print axioms fusedMap2068_checked
#print axioms certified2068
def sourceMap2068swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap2068swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2068swap_checked : acceptsGraphIso
    (source (graph core2068) (root 6) 4 0) DegreeOneSmallSpectrum931.graph sourceMap2068swap=true := by decide +kernel
theorem fusedMap2068swap_checked : acceptsGraphIso
    (fused (graph core2068) (root 6) 4 0) DegreeOneSmallSpectrum935.graph fusedMap2068swap=true := by decide +kernel
theorem certified2068swap : Certified (graph core2068) (root 6) 4 0 :=
  of_native_maps core2068 DegreeOneSmallSpectrum931.graph DegreeOneSmallSpectrum935.graph
    sourceMap2068swap fusedMap2068swap sourceMap2068swap_checked fusedMap2068swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2068
#print axioms sourceMap2068swap_checked
#print axioms fusedMap2068swap_checked
#print axioms certified2068swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
