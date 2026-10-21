/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1500 : Family 9 := level9.get ⟨229,by decide⟩
def sourceMap1500 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1500 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1500_checked : acceptsGraphIso
    (source (graph core1500) (root 9) 0 1) DegreeOneSmallSpectrum1409.graph sourceMap1500=true := by decide +kernel
theorem fusedMap1500_checked : acceptsGraphIso
    (fused (graph core1500) (root 9) 0 1) DegreeOneSmallSpectrum1414.graph fusedMap1500=true := by decide +kernel
theorem certified1500 : Certified (graph core1500) (root 9) 0 1 :=
  of_native_maps core1500 DegreeOneSmallSpectrum1409.graph DegreeOneSmallSpectrum1414.graph
    sourceMap1500 fusedMap1500 sourceMap1500_checked fusedMap1500_checked
    DegreeOneSmallComparisons.comparison1500
#print axioms sourceMap1500_checked
#print axioms fusedMap1500_checked
#print axioms certified1500
def sourceMap1500swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1500swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1500swap_checked : acceptsGraphIso
    (source (graph core1500) (root 9) 1 0) DegreeOneSmallSpectrum1409.graph sourceMap1500swap=true := by decide +kernel
theorem fusedMap1500swap_checked : acceptsGraphIso
    (fused (graph core1500) (root 9) 1 0) DegreeOneSmallSpectrum1414.graph fusedMap1500swap=true := by decide +kernel
theorem certified1500swap : Certified (graph core1500) (root 9) 1 0 :=
  of_native_maps core1500 DegreeOneSmallSpectrum1409.graph DegreeOneSmallSpectrum1414.graph
    sourceMap1500swap fusedMap1500swap sourceMap1500swap_checked fusedMap1500swap_checked
    DegreeOneSmallComparisons.comparison1500
#print axioms sourceMap1500swap_checked
#print axioms fusedMap1500swap_checked
#print axioms certified1500swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
