/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2079 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap2079 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2079 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2079_checked : acceptsGraphIso
    (source (graph core2079) (root 6) 0 4) DegreeOneSmallSpectrum987.graph sourceMap2079=true := by decide +kernel
theorem fusedMap2079_checked : acceptsGraphIso
    (fused (graph core2079) (root 6) 0 4) DegreeOneSmallSpectrum992.graph fusedMap2079=true := by decide +kernel
theorem certified2079 : Certified (graph core2079) (root 6) 0 4 :=
  of_native_maps core2079 DegreeOneSmallSpectrum987.graph DegreeOneSmallSpectrum992.graph
    sourceMap2079 fusedMap2079 sourceMap2079_checked fusedMap2079_checked
    DegreeTwoThreeFiniteComparisons.comparison2079
#print axioms sourceMap2079_checked
#print axioms fusedMap2079_checked
#print axioms certified2079
def sourceMap2079swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2079swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2079swap_checked : acceptsGraphIso
    (source (graph core2079) (root 6) 4 0) DegreeOneSmallSpectrum987.graph sourceMap2079swap=true := by decide +kernel
theorem fusedMap2079swap_checked : acceptsGraphIso
    (fused (graph core2079) (root 6) 4 0) DegreeOneSmallSpectrum992.graph fusedMap2079swap=true := by decide +kernel
theorem certified2079swap : Certified (graph core2079) (root 6) 4 0 :=
  of_native_maps core2079 DegreeOneSmallSpectrum987.graph DegreeOneSmallSpectrum992.graph
    sourceMap2079swap fusedMap2079swap sourceMap2079swap_checked fusedMap2079swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2079
#print axioms sourceMap2079swap_checked
#print axioms fusedMap2079swap_checked
#print axioms certified2079swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
