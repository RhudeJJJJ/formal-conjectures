/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2067 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap2067 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2067 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2067_checked : acceptsGraphIso
    (source (graph core2067) (root 6) 0 4) DegreeOneSmallSpectrum889.graph sourceMap2067=true := by decide +kernel
theorem fusedMap2067_checked : acceptsGraphIso
    (fused (graph core2067) (root 6) 0 4) DegreeOneSmallSpectrum894.graph fusedMap2067=true := by decide +kernel
theorem certified2067 : Certified (graph core2067) (root 6) 0 4 :=
  of_native_maps core2067 DegreeOneSmallSpectrum889.graph DegreeOneSmallSpectrum894.graph
    sourceMap2067 fusedMap2067 sourceMap2067_checked fusedMap2067_checked
    DegreeTwoThreeFiniteComparisons.comparison2067
#print axioms sourceMap2067_checked
#print axioms fusedMap2067_checked
#print axioms certified2067
def sourceMap2067swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap2067swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2067swap_checked : acceptsGraphIso
    (source (graph core2067) (root 6) 4 0) DegreeOneSmallSpectrum889.graph sourceMap2067swap=true := by decide +kernel
theorem fusedMap2067swap_checked : acceptsGraphIso
    (fused (graph core2067) (root 6) 4 0) DegreeOneSmallSpectrum894.graph fusedMap2067swap=true := by decide +kernel
theorem certified2067swap : Certified (graph core2067) (root 6) 4 0 :=
  of_native_maps core2067 DegreeOneSmallSpectrum889.graph DegreeOneSmallSpectrum894.graph
    sourceMap2067swap fusedMap2067swap sourceMap2067swap_checked fusedMap2067swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2067
#print axioms sourceMap2067swap_checked
#print axioms fusedMap2067swap_checked
#print axioms certified2067swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
