/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1470 : Family 9 := level9.get ⟨205,by decide⟩
def sourceMap1470 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1470 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1470_checked : acceptsGraphIso
    (source (graph core1470) (root 9) 0 1) DegreeOneSmallSpectrum1321.graph sourceMap1470=true := by decide +kernel
theorem fusedMap1470_checked : acceptsGraphIso
    (fused (graph core1470) (root 9) 0 1) DegreeOneSmallSpectrum1323.graph fusedMap1470=true := by decide +kernel
theorem certified1470 : Certified (graph core1470) (root 9) 0 1 :=
  of_native_maps core1470 DegreeOneSmallSpectrum1321.graph DegreeOneSmallSpectrum1323.graph
    sourceMap1470 fusedMap1470 sourceMap1470_checked fusedMap1470_checked
    DegreeOneSmallComparisons.comparison1470
#print axioms sourceMap1470_checked
#print axioms fusedMap1470_checked
#print axioms certified1470
def sourceMap1470swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1470swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1470swap_checked : acceptsGraphIso
    (source (graph core1470) (root 9) 1 0) DegreeOneSmallSpectrum1321.graph sourceMap1470swap=true := by decide +kernel
theorem fusedMap1470swap_checked : acceptsGraphIso
    (fused (graph core1470) (root 9) 1 0) DegreeOneSmallSpectrum1323.graph fusedMap1470swap=true := by decide +kernel
theorem certified1470swap : Certified (graph core1470) (root 9) 1 0 :=
  of_native_maps core1470 DegreeOneSmallSpectrum1321.graph DegreeOneSmallSpectrum1323.graph
    sourceMap1470swap fusedMap1470swap sourceMap1470swap_checked fusedMap1470swap_checked
    DegreeOneSmallComparisons.comparison1470
#print axioms sourceMap1470swap_checked
#print axioms fusedMap1470swap_checked
#print axioms certified1470swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
