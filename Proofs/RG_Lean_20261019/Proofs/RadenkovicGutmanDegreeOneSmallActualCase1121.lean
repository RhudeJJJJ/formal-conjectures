/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1121 : Family 8 := level8.get ⟨164,by decide⟩
def sourceMap1121 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1121 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1121_checked : acceptsGraphIso
    (source (graph core1121) (root 8) 0 2) DegreeOneSmallSpectrum1470.graph sourceMap1121=true := by decide +kernel
theorem fusedMap1121_checked : acceptsGraphIso
    (fused (graph core1121) (root 8) 0 2) DegreeOneSmallSpectrum1471.graph fusedMap1121=true := by decide +kernel
theorem certified1121 : Certified (graph core1121) (root 8) 0 2 :=
  of_native_maps core1121 DegreeOneSmallSpectrum1470.graph DegreeOneSmallSpectrum1471.graph
    sourceMap1121 fusedMap1121 sourceMap1121_checked fusedMap1121_checked
    DegreeOneSmallComparisons.comparison1121
#print axioms sourceMap1121_checked
#print axioms fusedMap1121_checked
#print axioms certified1121
def sourceMap1121swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1121swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1121swap_checked : acceptsGraphIso
    (source (graph core1121) (root 8) 2 0) DegreeOneSmallSpectrum1470.graph sourceMap1121swap=true := by decide +kernel
theorem fusedMap1121swap_checked : acceptsGraphIso
    (fused (graph core1121) (root 8) 2 0) DegreeOneSmallSpectrum1471.graph fusedMap1121swap=true := by decide +kernel
theorem certified1121swap : Certified (graph core1121) (root 8) 2 0 :=
  of_native_maps core1121 DegreeOneSmallSpectrum1470.graph DegreeOneSmallSpectrum1471.graph
    sourceMap1121swap fusedMap1121swap sourceMap1121swap_checked fusedMap1121swap_checked
    DegreeOneSmallComparisons.comparison1121
#print axioms sourceMap1121swap_checked
#print axioms fusedMap1121swap_checked
#print axioms certified1121swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
