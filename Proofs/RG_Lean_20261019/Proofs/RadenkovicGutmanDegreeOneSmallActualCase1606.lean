/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1606 : Family 9 := level9.get ⟨344,by decide⟩
def sourceMap1606 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1606 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1606_checked : acceptsGraphIso
    (source (graph core1606) (root 9) 0 1) DegreeOneSmallSpectrum1689.graph sourceMap1606=true := by decide +kernel
theorem fusedMap1606_checked : acceptsGraphIso
    (fused (graph core1606) (root 9) 0 1) DegreeOneSmallSpectrum1040.graph fusedMap1606=true := by decide +kernel
theorem certified1606 : Certified (graph core1606) (root 9) 0 1 :=
  of_native_maps core1606 DegreeOneSmallSpectrum1689.graph DegreeOneSmallSpectrum1040.graph
    sourceMap1606 fusedMap1606 sourceMap1606_checked fusedMap1606_checked
    DegreeOneSmallComparisons.comparison1606
#print axioms sourceMap1606_checked
#print axioms fusedMap1606_checked
#print axioms certified1606
def sourceMap1606swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1606swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1606swap_checked : acceptsGraphIso
    (source (graph core1606) (root 9) 1 0) DegreeOneSmallSpectrum1689.graph sourceMap1606swap=true := by decide +kernel
theorem fusedMap1606swap_checked : acceptsGraphIso
    (fused (graph core1606) (root 9) 1 0) DegreeOneSmallSpectrum1040.graph fusedMap1606swap=true := by decide +kernel
theorem certified1606swap : Certified (graph core1606) (root 9) 1 0 :=
  of_native_maps core1606 DegreeOneSmallSpectrum1689.graph DegreeOneSmallSpectrum1040.graph
    sourceMap1606swap fusedMap1606swap sourceMap1606swap_checked fusedMap1606swap_checked
    DegreeOneSmallComparisons.comparison1606
#print axioms sourceMap1606swap_checked
#print axioms fusedMap1606swap_checked
#print axioms certified1606swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
