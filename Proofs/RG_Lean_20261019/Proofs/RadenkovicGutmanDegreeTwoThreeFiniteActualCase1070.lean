/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1070 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap1070 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1070 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1070_checked : acceptsGraphIso
    (source (graph core1070) (root 7) 0 2) DegreeOneSmallSpectrum532.graph sourceMap1070=true := by decide +kernel
theorem fusedMap1070_checked : acceptsGraphIso
    (fused (graph core1070) (root 7) 0 2) DegreeOneSmallSpectrum534.graph fusedMap1070=true := by decide +kernel
theorem certified1070 : Certified (graph core1070) (root 7) 0 2 :=
  of_native_maps core1070 DegreeOneSmallSpectrum532.graph DegreeOneSmallSpectrum534.graph
    sourceMap1070 fusedMap1070 sourceMap1070_checked fusedMap1070_checked
    DegreeTwoThreeFiniteComparisons.comparison1070
#print axioms sourceMap1070_checked
#print axioms fusedMap1070_checked
#print axioms certified1070
def sourceMap1070swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1070swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1070swap_checked : acceptsGraphIso
    (source (graph core1070) (root 7) 2 0) DegreeOneSmallSpectrum532.graph sourceMap1070swap=true := by decide +kernel
theorem fusedMap1070swap_checked : acceptsGraphIso
    (fused (graph core1070) (root 7) 2 0) DegreeOneSmallSpectrum534.graph fusedMap1070swap=true := by decide +kernel
theorem certified1070swap : Certified (graph core1070) (root 7) 2 0 :=
  of_native_maps core1070 DegreeOneSmallSpectrum532.graph DegreeOneSmallSpectrum534.graph
    sourceMap1070swap fusedMap1070swap sourceMap1070swap_checked fusedMap1070swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1070
#print axioms sourceMap1070swap_checked
#print axioms fusedMap1070swap_checked
#print axioms certified1070swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
