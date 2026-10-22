/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1141 : Family 8 := level8.get ⟨152,by decide⟩
def sourceMap1141 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1141 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1141_checked : acceptsGraphIso
    (source (graph core1141) (root 8) 0 2) DegreeOneSmallSpectrum1412.graph sourceMap1141=true := by decide +kernel
theorem fusedMap1141_checked : acceptsGraphIso
    (fused (graph core1141) (root 8) 0 2) DegreeOneSmallSpectrum1414.graph fusedMap1141=true := by decide +kernel
theorem certified1141 : Certified (graph core1141) (root 8) 0 2 :=
  of_native_maps core1141 DegreeOneSmallSpectrum1412.graph DegreeOneSmallSpectrum1414.graph
    sourceMap1141 fusedMap1141 sourceMap1141_checked fusedMap1141_checked
    DegreeTwoThreeFiniteComparisons.comparison1141
#print axioms sourceMap1141_checked
#print axioms fusedMap1141_checked
#print axioms certified1141
def sourceMap1141swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1141swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1141swap_checked : acceptsGraphIso
    (source (graph core1141) (root 8) 2 0) DegreeOneSmallSpectrum1412.graph sourceMap1141swap=true := by decide +kernel
theorem fusedMap1141swap_checked : acceptsGraphIso
    (fused (graph core1141) (root 8) 2 0) DegreeOneSmallSpectrum1414.graph fusedMap1141swap=true := by decide +kernel
theorem certified1141swap : Certified (graph core1141) (root 8) 2 0 :=
  of_native_maps core1141 DegreeOneSmallSpectrum1412.graph DegreeOneSmallSpectrum1414.graph
    sourceMap1141swap fusedMap1141swap sourceMap1141swap_checked fusedMap1141swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1141
#print axioms sourceMap1141swap_checked
#print axioms fusedMap1141swap_checked
#print axioms certified1141swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
