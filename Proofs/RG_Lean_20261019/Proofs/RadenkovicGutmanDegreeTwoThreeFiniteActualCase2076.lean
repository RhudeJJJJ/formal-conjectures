/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2076 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap2076 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2076 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2076_checked : acceptsGraphIso
    (source (graph core2076) (root 6) 0 4) DegreeOneSmallSpectrum1408.graph sourceMap2076=true := by decide +kernel
theorem fusedMap2076_checked : acceptsGraphIso
    (fused (graph core2076) (root 6) 0 4) DegreeOneSmallSpectrum923.graph fusedMap2076=true := by decide +kernel
theorem certified2076 : Certified (graph core2076) (root 6) 0 4 :=
  of_native_maps core2076 DegreeOneSmallSpectrum1408.graph DegreeOneSmallSpectrum923.graph
    sourceMap2076 fusedMap2076 sourceMap2076_checked fusedMap2076_checked
    DegreeTwoThreeFiniteComparisons.comparison2076
#print axioms sourceMap2076_checked
#print axioms fusedMap2076_checked
#print axioms certified2076
def sourceMap2076swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2076swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2076swap_checked : acceptsGraphIso
    (source (graph core2076) (root 6) 4 0) DegreeOneSmallSpectrum1408.graph sourceMap2076swap=true := by decide +kernel
theorem fusedMap2076swap_checked : acceptsGraphIso
    (fused (graph core2076) (root 6) 4 0) DegreeOneSmallSpectrum923.graph fusedMap2076swap=true := by decide +kernel
theorem certified2076swap : Certified (graph core2076) (root 6) 4 0 :=
  of_native_maps core2076 DegreeOneSmallSpectrum1408.graph DegreeOneSmallSpectrum923.graph
    sourceMap2076swap fusedMap2076swap sourceMap2076swap_checked fusedMap2076swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2076
#print axioms sourceMap2076swap_checked
#print axioms fusedMap2076swap_checked
#print axioms certified2076swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
