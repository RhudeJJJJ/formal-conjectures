/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1077 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap1077 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,8,9,10,11,4,5,6,7,1,2,3] (sourceLabel 7 0 2 v)
def fusedMap1077 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (fusedLabel 7 0 2 v)
theorem sourceMap1077_checked : acceptsGraphIso
    (source (graph core1077) (root 7) 0 2) DegreeOneSmallSpectrum565.graph sourceMap1077=true := by decide +kernel
theorem fusedMap1077_checked : acceptsGraphIso
    (fused (graph core1077) (root 7) 0 2) DegreeOneSmallSpectrum586.graph fusedMap1077=true := by decide +kernel
theorem certified1077 : Certified (graph core1077) (root 7) 0 2 :=
  of_native_maps core1077 DegreeOneSmallSpectrum565.graph DegreeOneSmallSpectrum586.graph
    sourceMap1077 fusedMap1077 sourceMap1077_checked fusedMap1077_checked
    DegreeTwoThreeFiniteComparisons.comparison1077
#print axioms sourceMap1077_checked
#print axioms fusedMap1077_checked
#print axioms certified1077
def sourceMap1077swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,4,5,6,1,2,3,7] (sourceLabel 7 2 0 v)
def fusedMap1077swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (fusedLabel 7 2 0 v)
theorem sourceMap1077swap_checked : acceptsGraphIso
    (source (graph core1077) (root 7) 2 0) DegreeOneSmallSpectrum565.graph sourceMap1077swap=true := by decide +kernel
theorem fusedMap1077swap_checked : acceptsGraphIso
    (fused (graph core1077) (root 7) 2 0) DegreeOneSmallSpectrum586.graph fusedMap1077swap=true := by decide +kernel
theorem certified1077swap : Certified (graph core1077) (root 7) 2 0 :=
  of_native_maps core1077 DegreeOneSmallSpectrum565.graph DegreeOneSmallSpectrum586.graph
    sourceMap1077swap fusedMap1077swap sourceMap1077swap_checked fusedMap1077swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1077
#print axioms sourceMap1077swap_checked
#print axioms fusedMap1077swap_checked
#print axioms certified1077swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
