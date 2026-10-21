/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1426 : Family 9 := level9.get ⟨165,by decide⟩
def sourceMap1426 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1426 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1426_checked : acceptsGraphIso
    (source (graph core1426) (root 9) 0 1) DegreeOneSmallSpectrum1140.graph sourceMap1426=true := by decide +kernel
theorem fusedMap1426_checked : acceptsGraphIso
    (fused (graph core1426) (root 9) 0 1) DegreeOneSmallSpectrum1142.graph fusedMap1426=true := by decide +kernel
theorem certified1426 : Certified (graph core1426) (root 9) 0 1 :=
  of_native_maps core1426 DegreeOneSmallSpectrum1140.graph DegreeOneSmallSpectrum1142.graph
    sourceMap1426 fusedMap1426 sourceMap1426_checked fusedMap1426_checked
    DegreeOneSmallComparisons.comparison1426
#print axioms sourceMap1426_checked
#print axioms fusedMap1426_checked
#print axioms certified1426
def sourceMap1426swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1426swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1426swap_checked : acceptsGraphIso
    (source (graph core1426) (root 9) 1 0) DegreeOneSmallSpectrum1140.graph sourceMap1426swap=true := by decide +kernel
theorem fusedMap1426swap_checked : acceptsGraphIso
    (fused (graph core1426) (root 9) 1 0) DegreeOneSmallSpectrum1142.graph fusedMap1426swap=true := by decide +kernel
theorem certified1426swap : Certified (graph core1426) (root 9) 1 0 :=
  of_native_maps core1426 DegreeOneSmallSpectrum1140.graph DegreeOneSmallSpectrum1142.graph
    sourceMap1426swap fusedMap1426swap sourceMap1426swap_checked fusedMap1426swap_checked
    DegreeOneSmallComparisons.comparison1426
#print axioms sourceMap1426swap_checked
#print axioms fusedMap1426swap_checked
#print axioms certified1426swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
