/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2077 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap2077 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2077 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2077_checked : acceptsGraphIso
    (source (graph core2077) (root 6) 0 4) DegreeOneSmallSpectrum1459.graph sourceMap2077=true := by decide +kernel
theorem fusedMap2077_checked : acceptsGraphIso
    (fused (graph core2077) (root 6) 0 4) DegreeOneSmallSpectrum945.graph fusedMap2077=true := by decide +kernel
theorem certified2077 : Certified (graph core2077) (root 6) 0 4 :=
  of_native_maps core2077 DegreeOneSmallSpectrum1459.graph DegreeOneSmallSpectrum945.graph
    sourceMap2077 fusedMap2077 sourceMap2077_checked fusedMap2077_checked
    DegreeTwoThreeFiniteComparisons.comparison2077
#print axioms sourceMap2077_checked
#print axioms fusedMap2077_checked
#print axioms certified2077
def sourceMap2077swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2077swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2077swap_checked : acceptsGraphIso
    (source (graph core2077) (root 6) 4 0) DegreeOneSmallSpectrum1459.graph sourceMap2077swap=true := by decide +kernel
theorem fusedMap2077swap_checked : acceptsGraphIso
    (fused (graph core2077) (root 6) 4 0) DegreeOneSmallSpectrum945.graph fusedMap2077swap=true := by decide +kernel
theorem certified2077swap : Certified (graph core2077) (root 6) 4 0 :=
  of_native_maps core2077 DegreeOneSmallSpectrum1459.graph DegreeOneSmallSpectrum945.graph
    sourceMap2077swap fusedMap2077swap sourceMap2077swap_checked fusedMap2077swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2077
#print axioms sourceMap2077swap_checked
#print axioms fusedMap2077swap_checked
#print axioms certified2077swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
