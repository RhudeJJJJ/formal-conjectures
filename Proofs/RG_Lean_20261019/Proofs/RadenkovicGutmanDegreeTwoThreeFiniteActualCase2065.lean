/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2065 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap2065 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap2065 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap2065_checked : acceptsGraphIso
    (source (graph core2065) (root 5) 0 4) DegreeOneSmallSpectrum429.graph sourceMap2065=true := by decide +kernel
theorem fusedMap2065_checked : acceptsGraphIso
    (fused (graph core2065) (root 5) 0 4) DegreeOneSmallSpectrum434.graph fusedMap2065=true := by decide +kernel
theorem certified2065 : Certified (graph core2065) (root 5) 0 4 :=
  of_native_maps core2065 DegreeOneSmallSpectrum429.graph DegreeOneSmallSpectrum434.graph
    sourceMap2065 fusedMap2065 sourceMap2065_checked fusedMap2065_checked
    DegreeTwoThreeFiniteComparisons.comparison2065
#print axioms sourceMap2065_checked
#print axioms fusedMap2065_checked
#print axioms certified2065
def sourceMap2065swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap2065swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap2065swap_checked : acceptsGraphIso
    (source (graph core2065) (root 5) 4 0) DegreeOneSmallSpectrum429.graph sourceMap2065swap=true := by decide +kernel
theorem fusedMap2065swap_checked : acceptsGraphIso
    (fused (graph core2065) (root 5) 4 0) DegreeOneSmallSpectrum434.graph fusedMap2065swap=true := by decide +kernel
theorem certified2065swap : Certified (graph core2065) (root 5) 4 0 :=
  of_native_maps core2065 DegreeOneSmallSpectrum429.graph DegreeOneSmallSpectrum434.graph
    sourceMap2065swap fusedMap2065swap sourceMap2065swap_checked fusedMap2065swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2065
#print axioms sourceMap2065swap_checked
#print axioms fusedMap2065swap_checked
#print axioms certified2065swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
