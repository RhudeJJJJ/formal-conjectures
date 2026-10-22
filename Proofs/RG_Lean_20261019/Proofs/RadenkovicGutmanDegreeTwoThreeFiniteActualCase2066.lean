/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2066 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap2066 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,11,12,6,7,8,9,10] (sourceLabel 6 0 4 v)
def fusedMap2066 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2066_checked : acceptsGraphIso
    (source (graph core2066) (root 6) 0 4) DegreeOneSmallSpectrum978.graph sourceMap2066=true := by decide +kernel
theorem fusedMap2066_checked : acceptsGraphIso
    (fused (graph core2066) (root 6) 0 4) DegreeOneSmallSpectrum860.graph fusedMap2066=true := by decide +kernel
theorem certified2066 : Certified (graph core2066) (root 6) 0 4 :=
  of_native_maps core2066 DegreeOneSmallSpectrum978.graph DegreeOneSmallSpectrum860.graph
    sourceMap2066 fusedMap2066 sourceMap2066_checked fusedMap2066_checked
    DegreeTwoThreeFiniteComparisons.comparison2066
#print axioms sourceMap2066_checked
#print axioms fusedMap2066_checked
#print axioms certified2066
def sourceMap2066swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,11,6,7,8,9,10,12] (sourceLabel 6 4 0 v)
def fusedMap2066swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2066swap_checked : acceptsGraphIso
    (source (graph core2066) (root 6) 4 0) DegreeOneSmallSpectrum978.graph sourceMap2066swap=true := by decide +kernel
theorem fusedMap2066swap_checked : acceptsGraphIso
    (fused (graph core2066) (root 6) 4 0) DegreeOneSmallSpectrum860.graph fusedMap2066swap=true := by decide +kernel
theorem certified2066swap : Certified (graph core2066) (root 6) 4 0 :=
  of_native_maps core2066 DegreeOneSmallSpectrum978.graph DegreeOneSmallSpectrum860.graph
    sourceMap2066swap fusedMap2066swap sourceMap2066swap_checked fusedMap2066swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2066
#print axioms sourceMap2066swap_checked
#print axioms fusedMap2066swap_checked
#print axioms certified2066swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
