/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1744 : Family 9 := level9.get ⟨565,by decide⟩
def sourceMap1744 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1744 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1744_checked : acceptsGraphIso
    (source (graph core1744) (root 9) 0 1) DegreeOneSmallSpectrum1623.graph sourceMap1744=true := by decide +kernel
theorem fusedMap1744_checked : acceptsGraphIso
    (fused (graph core1744) (root 9) 0 1) DegreeOneSmallSpectrum1624.graph fusedMap1744=true := by decide +kernel
theorem certified1744 : Certified (graph core1744) (root 9) 0 1 :=
  of_native_maps core1744 DegreeOneSmallSpectrum1623.graph DegreeOneSmallSpectrum1624.graph
    sourceMap1744 fusedMap1744 sourceMap1744_checked fusedMap1744_checked
    DegreeOneSmallComparisons.comparison1744
#print axioms sourceMap1744_checked
#print axioms fusedMap1744_checked
#print axioms certified1744
def sourceMap1744swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1744swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1744swap_checked : acceptsGraphIso
    (source (graph core1744) (root 9) 1 0) DegreeOneSmallSpectrum1623.graph sourceMap1744swap=true := by decide +kernel
theorem fusedMap1744swap_checked : acceptsGraphIso
    (fused (graph core1744) (root 9) 1 0) DegreeOneSmallSpectrum1624.graph fusedMap1744swap=true := by decide +kernel
theorem certified1744swap : Certified (graph core1744) (root 9) 1 0 :=
  of_native_maps core1744 DegreeOneSmallSpectrum1623.graph DegreeOneSmallSpectrum1624.graph
    sourceMap1744swap fusedMap1744swap sourceMap1744swap_checked fusedMap1744swap_checked
    DegreeOneSmallComparisons.comparison1744
#print axioms sourceMap1744swap_checked
#print axioms fusedMap1744swap_checked
#print axioms certified1744swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
