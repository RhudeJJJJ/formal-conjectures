/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1188 : Family 8 := level8.get ⟨240,by decide⟩
def sourceMap1188 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1188 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1188_checked : acceptsGraphIso
    (source (graph core1188) (root 8) 0 1) SmallGeFourSpectrum179.graph sourceMap1188=true := by decide +kernel
theorem fusedMap1188_checked : acceptsGraphIso
    (fused (graph core1188) (root 8) 0 1) SmallGeFourSpectrum180.graph fusedMap1188=true := by decide +kernel
theorem certified1188 : Certified (graph core1188) (root 8) 0 1 :=
  of_native_maps core1188 SmallGeFourSpectrum179.graph SmallGeFourSpectrum180.graph
    sourceMap1188 fusedMap1188 sourceMap1188_checked fusedMap1188_checked
    DegreeOneSmallComparisons.comparison1188
#print axioms sourceMap1188_checked
#print axioms fusedMap1188_checked
#print axioms certified1188
def sourceMap1188swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1188swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1188swap_checked : acceptsGraphIso
    (source (graph core1188) (root 8) 1 0) SmallGeFourSpectrum179.graph sourceMap1188swap=true := by decide +kernel
theorem fusedMap1188swap_checked : acceptsGraphIso
    (fused (graph core1188) (root 8) 1 0) SmallGeFourSpectrum180.graph fusedMap1188swap=true := by decide +kernel
theorem certified1188swap : Certified (graph core1188) (root 8) 1 0 :=
  of_native_maps core1188 SmallGeFourSpectrum179.graph SmallGeFourSpectrum180.graph
    sourceMap1188swap fusedMap1188swap sourceMap1188swap_checked fusedMap1188swap_checked
    DegreeOneSmallComparisons.comparison1188
#print axioms sourceMap1188swap_checked
#print axioms fusedMap1188swap_checked
#print axioms certified1188swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
