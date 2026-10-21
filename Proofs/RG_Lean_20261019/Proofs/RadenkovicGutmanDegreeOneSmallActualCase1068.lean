/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1068 : Family 8 := level8.get ⟨134,by decide⟩
def sourceMap1068 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap1068 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1068_checked : acceptsGraphIso
    (source (graph core1068) (root 8) 0 1) DegreeOneSmallSpectrum785.graph sourceMap1068=true := by decide +kernel
theorem fusedMap1068_checked : acceptsGraphIso
    (fused (graph core1068) (root 8) 0 1) DegreeOneSmallSpectrum502.graph fusedMap1068=true := by decide +kernel
theorem certified1068 : Certified (graph core1068) (root 8) 0 1 :=
  of_native_maps core1068 DegreeOneSmallSpectrum785.graph DegreeOneSmallSpectrum502.graph
    sourceMap1068 fusedMap1068 sourceMap1068_checked fusedMap1068_checked
    DegreeOneSmallComparisons.comparison1068
#print axioms sourceMap1068_checked
#print axioms fusedMap1068_checked
#print axioms certified1068
def sourceMap1068swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap1068swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1068swap_checked : acceptsGraphIso
    (source (graph core1068) (root 8) 1 0) DegreeOneSmallSpectrum785.graph sourceMap1068swap=true := by decide +kernel
theorem fusedMap1068swap_checked : acceptsGraphIso
    (fused (graph core1068) (root 8) 1 0) DegreeOneSmallSpectrum502.graph fusedMap1068swap=true := by decide +kernel
theorem certified1068swap : Certified (graph core1068) (root 8) 1 0 :=
  of_native_maps core1068 DegreeOneSmallSpectrum785.graph DegreeOneSmallSpectrum502.graph
    sourceMap1068swap fusedMap1068swap sourceMap1068swap_checked fusedMap1068swap_checked
    DegreeOneSmallComparisons.comparison1068
#print axioms sourceMap1068swap_checked
#print axioms fusedMap1068swap_checked
#print axioms certified1068swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
