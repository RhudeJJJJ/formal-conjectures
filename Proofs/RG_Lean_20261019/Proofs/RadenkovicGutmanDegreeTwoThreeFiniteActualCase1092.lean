/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1092 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap1092 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (sourceLabel 7 0 2 v)
def fusedMap1092 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1092_checked : acceptsGraphIso
    (source (graph core1092) (root 7) 0 2) DegreeOneSmallSpectrum825.graph sourceMap1092=true := by decide +kernel
theorem fusedMap1092_checked : acceptsGraphIso
    (fused (graph core1092) (root 7) 0 2) DegreeOneSmallSpectrum564.graph fusedMap1092=true := by decide +kernel
theorem certified1092 : Certified (graph core1092) (root 7) 0 2 :=
  of_native_maps core1092 DegreeOneSmallSpectrum825.graph DegreeOneSmallSpectrum564.graph
    sourceMap1092 fusedMap1092 sourceMap1092_checked fusedMap1092_checked
    DegreeTwoThreeFiniteComparisons.comparison1092
#print axioms sourceMap1092_checked
#print axioms fusedMap1092_checked
#print axioms certified1092
def sourceMap1092swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6,11] (sourceLabel 7 2 0 v)
def fusedMap1092swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1092swap_checked : acceptsGraphIso
    (source (graph core1092) (root 7) 2 0) DegreeOneSmallSpectrum825.graph sourceMap1092swap=true := by decide +kernel
theorem fusedMap1092swap_checked : acceptsGraphIso
    (fused (graph core1092) (root 7) 2 0) DegreeOneSmallSpectrum564.graph fusedMap1092swap=true := by decide +kernel
theorem certified1092swap : Certified (graph core1092) (root 7) 2 0 :=
  of_native_maps core1092 DegreeOneSmallSpectrum825.graph DegreeOneSmallSpectrum564.graph
    sourceMap1092swap fusedMap1092swap sourceMap1092swap_checked fusedMap1092swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1092
#print axioms sourceMap1092swap_checked
#print axioms fusedMap1092swap_checked
#print axioms certified1092swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
