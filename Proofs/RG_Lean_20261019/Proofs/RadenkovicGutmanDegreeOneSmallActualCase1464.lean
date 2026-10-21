/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1464 : Family 9 := level9.get ⟨201,by decide⟩
def sourceMap1464 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1464 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1464_checked : acceptsGraphIso
    (source (graph core1464) (root 9) 0 1) DegreeOneSmallSpectrum1304.graph sourceMap1464=true := by decide +kernel
theorem fusedMap1464_checked : acceptsGraphIso
    (fused (graph core1464) (root 9) 0 1) DegreeOneSmallSpectrum1306.graph fusedMap1464=true := by decide +kernel
theorem certified1464 : Certified (graph core1464) (root 9) 0 1 :=
  of_native_maps core1464 DegreeOneSmallSpectrum1304.graph DegreeOneSmallSpectrum1306.graph
    sourceMap1464 fusedMap1464 sourceMap1464_checked fusedMap1464_checked
    DegreeOneSmallComparisons.comparison1464
#print axioms sourceMap1464_checked
#print axioms fusedMap1464_checked
#print axioms certified1464
def sourceMap1464swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1464swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1464swap_checked : acceptsGraphIso
    (source (graph core1464) (root 9) 1 0) DegreeOneSmallSpectrum1304.graph sourceMap1464swap=true := by decide +kernel
theorem fusedMap1464swap_checked : acceptsGraphIso
    (fused (graph core1464) (root 9) 1 0) DegreeOneSmallSpectrum1306.graph fusedMap1464swap=true := by decide +kernel
theorem certified1464swap : Certified (graph core1464) (root 9) 1 0 :=
  of_native_maps core1464 DegreeOneSmallSpectrum1304.graph DegreeOneSmallSpectrum1306.graph
    sourceMap1464swap fusedMap1464swap sourceMap1464swap_checked fusedMap1464swap_checked
    DegreeOneSmallComparisons.comparison1464
#print axioms sourceMap1464swap_checked
#print axioms fusedMap1464swap_checked
#print axioms certified1464swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
