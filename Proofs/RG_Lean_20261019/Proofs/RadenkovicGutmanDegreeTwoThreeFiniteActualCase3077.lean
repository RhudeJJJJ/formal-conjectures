/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3077 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3077 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (sourceLabel 3 0 5 v)
def fusedMap3077 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 0 5 v)
theorem sourceMap3077_checked : acceptsGraphIso
    (source (graph core3077) (root 3) 0 5) DegreeOneSmallSpectrum207.graph sourceMap3077=true := by decide +kernel
theorem fusedMap3077_checked : acceptsGraphIso
    (fused (graph core3077) (root 3) 0 5) DegreeOneSmallSpectrum165.graph fusedMap3077=true := by decide +kernel
theorem certified3077 : Certified (graph core3077) (root 3) 0 5 :=
  of_native_maps core3077 DegreeOneSmallSpectrum207.graph DegreeOneSmallSpectrum165.graph
    sourceMap3077 fusedMap3077 sourceMap3077_checked fusedMap3077_checked
    DegreeTwoThreeFiniteComparisons.comparison3077
#print axioms sourceMap3077_checked
#print axioms fusedMap3077_checked
#print axioms certified3077
def sourceMap3077swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,7,8,9,10,6] (sourceLabel 3 5 0 v)
def fusedMap3077swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 5 0 v)
theorem sourceMap3077swap_checked : acceptsGraphIso
    (source (graph core3077) (root 3) 5 0) DegreeOneSmallSpectrum207.graph sourceMap3077swap=true := by decide +kernel
theorem fusedMap3077swap_checked : acceptsGraphIso
    (fused (graph core3077) (root 3) 5 0) DegreeOneSmallSpectrum165.graph fusedMap3077swap=true := by decide +kernel
theorem certified3077swap : Certified (graph core3077) (root 3) 5 0 :=
  of_native_maps core3077 DegreeOneSmallSpectrum207.graph DegreeOneSmallSpectrum165.graph
    sourceMap3077swap fusedMap3077swap sourceMap3077swap_checked fusedMap3077swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3077
#print axioms sourceMap3077swap_checked
#print axioms fusedMap3077swap_checked
#print axioms certified3077swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
