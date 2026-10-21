/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1488 : Family 9 := level9.get ⟨219,by decide⟩
def sourceMap1488 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1488 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1488_checked : acceptsGraphIso
    (source (graph core1488) (root 9) 0 1) DegreeOneSmallSpectrum1375.graph sourceMap1488=true := by decide +kernel
theorem fusedMap1488_checked : acceptsGraphIso
    (fused (graph core1488) (root 9) 0 1) DegreeOneSmallSpectrum1380.graph fusedMap1488=true := by decide +kernel
theorem certified1488 : Certified (graph core1488) (root 9) 0 1 :=
  of_native_maps core1488 DegreeOneSmallSpectrum1375.graph DegreeOneSmallSpectrum1380.graph
    sourceMap1488 fusedMap1488 sourceMap1488_checked fusedMap1488_checked
    DegreeOneSmallComparisons.comparison1488
#print axioms sourceMap1488_checked
#print axioms fusedMap1488_checked
#print axioms certified1488
def sourceMap1488swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1488swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1488swap_checked : acceptsGraphIso
    (source (graph core1488) (root 9) 1 0) DegreeOneSmallSpectrum1375.graph sourceMap1488swap=true := by decide +kernel
theorem fusedMap1488swap_checked : acceptsGraphIso
    (fused (graph core1488) (root 9) 1 0) DegreeOneSmallSpectrum1380.graph fusedMap1488swap=true := by decide +kernel
theorem certified1488swap : Certified (graph core1488) (root 9) 1 0 :=
  of_native_maps core1488 DegreeOneSmallSpectrum1375.graph DegreeOneSmallSpectrum1380.graph
    sourceMap1488swap fusedMap1488swap sourceMap1488swap_checked fusedMap1488swap_checked
    DegreeOneSmallComparisons.comparison1488
#print axioms sourceMap1488swap_checked
#print axioms fusedMap1488swap_checked
#print axioms certified1488swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
