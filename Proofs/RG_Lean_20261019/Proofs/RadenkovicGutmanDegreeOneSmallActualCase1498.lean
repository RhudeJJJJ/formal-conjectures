/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1498 : Family 9 := level9.get ⟨228,by decide⟩
def sourceMap1498 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1498 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1498_checked : acceptsGraphIso
    (source (graph core1498) (root 9) 0 1) DegreeOneSmallSpectrum1406.graph sourceMap1498=true := by decide +kernel
theorem fusedMap1498_checked : acceptsGraphIso
    (fused (graph core1498) (root 9) 0 1) DegreeOneSmallSpectrum1408.graph fusedMap1498=true := by decide +kernel
theorem certified1498 : Certified (graph core1498) (root 9) 0 1 :=
  of_native_maps core1498 DegreeOneSmallSpectrum1406.graph DegreeOneSmallSpectrum1408.graph
    sourceMap1498 fusedMap1498 sourceMap1498_checked fusedMap1498_checked
    DegreeOneSmallComparisons.comparison1498
#print axioms sourceMap1498_checked
#print axioms fusedMap1498_checked
#print axioms certified1498
def sourceMap1498swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1498swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1498swap_checked : acceptsGraphIso
    (source (graph core1498) (root 9) 1 0) DegreeOneSmallSpectrum1406.graph sourceMap1498swap=true := by decide +kernel
theorem fusedMap1498swap_checked : acceptsGraphIso
    (fused (graph core1498) (root 9) 1 0) DegreeOneSmallSpectrum1408.graph fusedMap1498swap=true := by decide +kernel
theorem certified1498swap : Certified (graph core1498) (root 9) 1 0 :=
  of_native_maps core1498 DegreeOneSmallSpectrum1406.graph DegreeOneSmallSpectrum1408.graph
    sourceMap1498swap fusedMap1498swap sourceMap1498swap_checked fusedMap1498swap_checked
    DegreeOneSmallComparisons.comparison1498
#print axioms sourceMap1498swap_checked
#print axioms fusedMap1498swap_checked
#print axioms certified1498swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
