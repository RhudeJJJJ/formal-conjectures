/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1294 : Family 9 := level9.get ⟨61,by decide⟩
def sourceMap1294 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1294 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1294_checked : acceptsGraphIso
    (source (graph core1294) (root 9) 0 1) DegreeOneSmallSpectrum1273.graph sourceMap1294=true := by decide +kernel
theorem fusedMap1294_checked : acceptsGraphIso
    (fused (graph core1294) (root 9) 0 1) DegreeOneSmallSpectrum889.graph fusedMap1294=true := by decide +kernel
theorem certified1294 : Certified (graph core1294) (root 9) 0 1 :=
  of_native_maps core1294 DegreeOneSmallSpectrum1273.graph DegreeOneSmallSpectrum889.graph
    sourceMap1294 fusedMap1294 sourceMap1294_checked fusedMap1294_checked
    DegreeOneSmallComparisons.comparison1294
#print axioms sourceMap1294_checked
#print axioms fusedMap1294_checked
#print axioms certified1294
def sourceMap1294swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1294swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1294swap_checked : acceptsGraphIso
    (source (graph core1294) (root 9) 1 0) DegreeOneSmallSpectrum1273.graph sourceMap1294swap=true := by decide +kernel
theorem fusedMap1294swap_checked : acceptsGraphIso
    (fused (graph core1294) (root 9) 1 0) DegreeOneSmallSpectrum889.graph fusedMap1294swap=true := by decide +kernel
theorem certified1294swap : Certified (graph core1294) (root 9) 1 0 :=
  of_native_maps core1294 DegreeOneSmallSpectrum1273.graph DegreeOneSmallSpectrum889.graph
    sourceMap1294swap fusedMap1294swap sourceMap1294swap_checked fusedMap1294swap_checked
    DegreeOneSmallComparisons.comparison1294
#print axioms sourceMap1294swap_checked
#print axioms fusedMap1294swap_checked
#print axioms certified1294swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
