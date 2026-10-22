/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1065 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap1065 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1065 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1065_checked : acceptsGraphIso
    (source (graph core1065) (root 7) 0 2) DegreeOneSmallSpectrum425.graph sourceMap1065=true := by decide +kernel
theorem fusedMap1065_checked : acceptsGraphIso
    (fused (graph core1065) (root 7) 0 2) DegreeOneSmallSpectrum427.graph fusedMap1065=true := by decide +kernel
theorem certified1065 : Certified (graph core1065) (root 7) 0 2 :=
  of_native_maps core1065 DegreeOneSmallSpectrum425.graph DegreeOneSmallSpectrum427.graph
    sourceMap1065 fusedMap1065 sourceMap1065_checked fusedMap1065_checked
    DegreeTwoThreeFiniteComparisons.comparison1065
#print axioms sourceMap1065_checked
#print axioms fusedMap1065_checked
#print axioms certified1065
def sourceMap1065swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1065swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1065swap_checked : acceptsGraphIso
    (source (graph core1065) (root 7) 2 0) DegreeOneSmallSpectrum425.graph sourceMap1065swap=true := by decide +kernel
theorem fusedMap1065swap_checked : acceptsGraphIso
    (fused (graph core1065) (root 7) 2 0) DegreeOneSmallSpectrum427.graph fusedMap1065swap=true := by decide +kernel
theorem certified1065swap : Certified (graph core1065) (root 7) 2 0 :=
  of_native_maps core1065 DegreeOneSmallSpectrum425.graph DegreeOneSmallSpectrum427.graph
    sourceMap1065swap fusedMap1065swap sourceMap1065swap_checked fusedMap1065swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1065
#print axioms sourceMap1065swap_checked
#print axioms fusedMap1065swap_checked
#print axioms certified1065swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
