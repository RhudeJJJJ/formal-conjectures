/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1414 : Family 9 := level9.get ⟨157,by decide⟩
def sourceMap1414 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1414 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1414_checked : acceptsGraphIso
    (source (graph core1414) (root 9) 0 1) DegreeOneSmallSpectrum1093.graph sourceMap1414=true := by decide +kernel
theorem fusedMap1414_checked : acceptsGraphIso
    (fused (graph core1414) (root 9) 0 1) DegreeOneSmallSpectrum1095.graph fusedMap1414=true := by decide +kernel
theorem certified1414 : Certified (graph core1414) (root 9) 0 1 :=
  of_native_maps core1414 DegreeOneSmallSpectrum1093.graph DegreeOneSmallSpectrum1095.graph
    sourceMap1414 fusedMap1414 sourceMap1414_checked fusedMap1414_checked
    DegreeOneSmallComparisons.comparison1414
#print axioms sourceMap1414_checked
#print axioms fusedMap1414_checked
#print axioms certified1414
def sourceMap1414swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1414swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1414swap_checked : acceptsGraphIso
    (source (graph core1414) (root 9) 1 0) DegreeOneSmallSpectrum1093.graph sourceMap1414swap=true := by decide +kernel
theorem fusedMap1414swap_checked : acceptsGraphIso
    (fused (graph core1414) (root 9) 1 0) DegreeOneSmallSpectrum1095.graph fusedMap1414swap=true := by decide +kernel
theorem certified1414swap : Certified (graph core1414) (root 9) 1 0 :=
  of_native_maps core1414 DegreeOneSmallSpectrum1093.graph DegreeOneSmallSpectrum1095.graph
    sourceMap1414swap fusedMap1414swap sourceMap1414swap_checked fusedMap1414swap_checked
    DegreeOneSmallComparisons.comparison1414
#print axioms sourceMap1414swap_checked
#print axioms fusedMap1414swap_checked
#print axioms certified1414swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
