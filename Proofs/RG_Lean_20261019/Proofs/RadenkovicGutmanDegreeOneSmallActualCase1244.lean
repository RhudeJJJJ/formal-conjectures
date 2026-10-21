/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1244 : Family 9 := level9.get ⟨27,by decide⟩
def sourceMap1244 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1244 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1244_checked : acceptsGraphIso
    (source (graph core1244) (root 9) 0 1) DegreeOneSmallSpectrum927.graph sourceMap1244=true := by decide +kernel
theorem fusedMap1244_checked : acceptsGraphIso
    (fused (graph core1244) (root 9) 0 1) DegreeOneSmallSpectrum965.graph fusedMap1244=true := by decide +kernel
theorem certified1244 : Certified (graph core1244) (root 9) 0 1 :=
  of_native_maps core1244 DegreeOneSmallSpectrum927.graph DegreeOneSmallSpectrum965.graph
    sourceMap1244 fusedMap1244 sourceMap1244_checked fusedMap1244_checked
    DegreeOneSmallComparisons.comparison1244
#print axioms sourceMap1244_checked
#print axioms fusedMap1244_checked
#print axioms certified1244
def sourceMap1244swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1244swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1244swap_checked : acceptsGraphIso
    (source (graph core1244) (root 9) 1 0) DegreeOneSmallSpectrum927.graph sourceMap1244swap=true := by decide +kernel
theorem fusedMap1244swap_checked : acceptsGraphIso
    (fused (graph core1244) (root 9) 1 0) DegreeOneSmallSpectrum965.graph fusedMap1244swap=true := by decide +kernel
theorem certified1244swap : Certified (graph core1244) (root 9) 1 0 :=
  of_native_maps core1244 DegreeOneSmallSpectrum927.graph DegreeOneSmallSpectrum965.graph
    sourceMap1244swap fusedMap1244swap sourceMap1244swap_checked fusedMap1244swap_checked
    DegreeOneSmallComparisons.comparison1244
#print axioms sourceMap1244swap_checked
#print axioms fusedMap1244swap_checked
#print axioms certified1244swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
