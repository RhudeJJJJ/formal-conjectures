/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1088 : Family 8 := level8.get ⟨144,by decide⟩
def sourceMap1088 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap1088 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1088_checked : acceptsGraphIso
    (source (graph core1088) (root 8) 0 1) DegreeOneSmallSpectrum806.graph sourceMap1088=true := by decide +kernel
theorem fusedMap1088_checked : acceptsGraphIso
    (fused (graph core1088) (root 8) 0 1) DegreeOneSmallSpectrum524.graph fusedMap1088=true := by decide +kernel
theorem certified1088 : Certified (graph core1088) (root 8) 0 1 :=
  of_native_maps core1088 DegreeOneSmallSpectrum806.graph DegreeOneSmallSpectrum524.graph
    sourceMap1088 fusedMap1088 sourceMap1088_checked fusedMap1088_checked
    DegreeOneSmallComparisons.comparison1088
#print axioms sourceMap1088_checked
#print axioms fusedMap1088_checked
#print axioms certified1088
def sourceMap1088swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap1088swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1088swap_checked : acceptsGraphIso
    (source (graph core1088) (root 8) 1 0) DegreeOneSmallSpectrum806.graph sourceMap1088swap=true := by decide +kernel
theorem fusedMap1088swap_checked : acceptsGraphIso
    (fused (graph core1088) (root 8) 1 0) DegreeOneSmallSpectrum524.graph fusedMap1088swap=true := by decide +kernel
theorem certified1088swap : Certified (graph core1088) (root 8) 1 0 :=
  of_native_maps core1088 DegreeOneSmallSpectrum806.graph DegreeOneSmallSpectrum524.graph
    sourceMap1088swap fusedMap1088swap sourceMap1088swap_checked fusedMap1088swap_checked
    DegreeOneSmallComparisons.comparison1088
#print axioms sourceMap1088swap_checked
#print axioms fusedMap1088swap_checked
#print axioms certified1088swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
