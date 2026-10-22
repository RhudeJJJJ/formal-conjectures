/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1076 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap1076 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,7,4,5,6] (sourceLabel 7 0 2 v)
def fusedMap1076 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (fusedLabel 7 0 2 v)
theorem sourceMap1076_checked : acceptsGraphIso
    (source (graph core1076) (root 7) 0 2) DegreeOneSmallSpectrum561.graph sourceMap1076=true := by decide +kernel
theorem fusedMap1076_checked : acceptsGraphIso
    (fused (graph core1076) (root 7) 0 2) DegreeOneSmallSpectrum585.graph fusedMap1076=true := by decide +kernel
theorem certified1076 : Certified (graph core1076) (root 7) 0 2 :=
  of_native_maps core1076 DegreeOneSmallSpectrum561.graph DegreeOneSmallSpectrum585.graph
    sourceMap1076 fusedMap1076 sourceMap1076_checked fusedMap1076_checked
    DegreeTwoThreeFiniteComparisons.comparison1076
#print axioms sourceMap1076_checked
#print axioms fusedMap1076_checked
#print axioms certified1076
def sourceMap1076swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 7 2 0 v)
def fusedMap1076swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (fusedLabel 7 2 0 v)
theorem sourceMap1076swap_checked : acceptsGraphIso
    (source (graph core1076) (root 7) 2 0) DegreeOneSmallSpectrum561.graph sourceMap1076swap=true := by decide +kernel
theorem fusedMap1076swap_checked : acceptsGraphIso
    (fused (graph core1076) (root 7) 2 0) DegreeOneSmallSpectrum585.graph fusedMap1076swap=true := by decide +kernel
theorem certified1076swap : Certified (graph core1076) (root 7) 2 0 :=
  of_native_maps core1076 DegreeOneSmallSpectrum561.graph DegreeOneSmallSpectrum585.graph
    sourceMap1076swap fusedMap1076swap sourceMap1076swap_checked fusedMap1076swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1076
#print axioms sourceMap1076swap_checked
#print axioms fusedMap1076swap_checked
#print axioms certified1076swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
