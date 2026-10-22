/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2081 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap2081 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2081 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2081_checked : acceptsGraphIso
    (source (graph core2081) (root 6) 0 4) DegreeOneSmallSpectrum1083.graph sourceMap2081=true := by decide +kernel
theorem fusedMap2081_checked : acceptsGraphIso
    (fused (graph core2081) (root 6) 0 4) DegreeOneSmallSpectrum1088.graph fusedMap2081=true := by decide +kernel
theorem certified2081 : Certified (graph core2081) (root 6) 0 4 :=
  of_native_maps core2081 DegreeOneSmallSpectrum1083.graph DegreeOneSmallSpectrum1088.graph
    sourceMap2081 fusedMap2081 sourceMap2081_checked fusedMap2081_checked
    DegreeTwoThreeFiniteComparisons.comparison2081
#print axioms sourceMap2081_checked
#print axioms fusedMap2081_checked
#print axioms certified2081
def sourceMap2081swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2081swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2081swap_checked : acceptsGraphIso
    (source (graph core2081) (root 6) 4 0) DegreeOneSmallSpectrum1083.graph sourceMap2081swap=true := by decide +kernel
theorem fusedMap2081swap_checked : acceptsGraphIso
    (fused (graph core2081) (root 6) 4 0) DegreeOneSmallSpectrum1088.graph fusedMap2081swap=true := by decide +kernel
theorem certified2081swap : Certified (graph core2081) (root 6) 4 0 :=
  of_native_maps core2081 DegreeOneSmallSpectrum1083.graph DegreeOneSmallSpectrum1088.graph
    sourceMap2081swap fusedMap2081swap sourceMap2081swap_checked fusedMap2081swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2081
#print axioms sourceMap2081swap_checked
#print axioms fusedMap2081swap_checked
#print axioms certified2081swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
