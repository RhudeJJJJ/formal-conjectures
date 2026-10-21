/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1610 : Family 9 := level9.get ⟨354,by decide⟩
def sourceMap1610 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1610 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1610_checked : acceptsGraphIso
    (source (graph core1610) (root 9) 0 1) DegreeOneSmallSpectrum1710.graph sourceMap1610=true := by decide +kernel
theorem fusedMap1610_checked : acceptsGraphIso
    (fused (graph core1610) (root 9) 0 1) DegreeOneSmallSpectrum1083.graph fusedMap1610=true := by decide +kernel
theorem certified1610 : Certified (graph core1610) (root 9) 0 1 :=
  of_native_maps core1610 DegreeOneSmallSpectrum1710.graph DegreeOneSmallSpectrum1083.graph
    sourceMap1610 fusedMap1610 sourceMap1610_checked fusedMap1610_checked
    DegreeOneSmallComparisons.comparison1610
#print axioms sourceMap1610_checked
#print axioms fusedMap1610_checked
#print axioms certified1610
def sourceMap1610swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1610swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1610swap_checked : acceptsGraphIso
    (source (graph core1610) (root 9) 1 0) DegreeOneSmallSpectrum1710.graph sourceMap1610swap=true := by decide +kernel
theorem fusedMap1610swap_checked : acceptsGraphIso
    (fused (graph core1610) (root 9) 1 0) DegreeOneSmallSpectrum1083.graph fusedMap1610swap=true := by decide +kernel
theorem certified1610swap : Certified (graph core1610) (root 9) 1 0 :=
  of_native_maps core1610 DegreeOneSmallSpectrum1710.graph DegreeOneSmallSpectrum1083.graph
    sourceMap1610swap fusedMap1610swap sourceMap1610swap_checked fusedMap1610swap_checked
    DegreeOneSmallComparisons.comparison1610
#print axioms sourceMap1610swap_checked
#print axioms fusedMap1610swap_checked
#print axioms certified1610swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
