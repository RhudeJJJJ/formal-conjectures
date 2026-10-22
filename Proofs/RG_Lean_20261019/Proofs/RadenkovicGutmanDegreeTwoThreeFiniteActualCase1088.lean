/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1088 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap1088 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1088 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1088_checked : acceptsGraphIso
    (source (graph core1088) (root 7) 0 2) SmallGeFourSpectrum188.graph sourceMap1088=true := by decide +kernel
theorem fusedMap1088_checked : acceptsGraphIso
    (fused (graph core1088) (root 7) 0 2) SmallGeFourSpectrum101.graph fusedMap1088=true := by decide +kernel
theorem certified1088 : Certified (graph core1088) (root 7) 0 2 :=
  of_native_maps core1088 SmallGeFourSpectrum188.graph SmallGeFourSpectrum101.graph
    sourceMap1088 fusedMap1088 sourceMap1088_checked fusedMap1088_checked
    DegreeTwoThreeFiniteComparisons.comparison1088
#print axioms sourceMap1088_checked
#print axioms fusedMap1088_checked
#print axioms certified1088
def sourceMap1088swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1088swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1088swap_checked : acceptsGraphIso
    (source (graph core1088) (root 7) 2 0) SmallGeFourSpectrum188.graph sourceMap1088swap=true := by decide +kernel
theorem fusedMap1088swap_checked : acceptsGraphIso
    (fused (graph core1088) (root 7) 2 0) SmallGeFourSpectrum101.graph fusedMap1088swap=true := by decide +kernel
theorem certified1088swap : Certified (graph core1088) (root 7) 2 0 :=
  of_native_maps core1088 SmallGeFourSpectrum188.graph SmallGeFourSpectrum101.graph
    sourceMap1088swap fusedMap1088swap sourceMap1088swap_checked fusedMap1088swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1088
#print axioms sourceMap1088swap_checked
#print axioms fusedMap1088swap_checked
#print axioms certified1088swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
