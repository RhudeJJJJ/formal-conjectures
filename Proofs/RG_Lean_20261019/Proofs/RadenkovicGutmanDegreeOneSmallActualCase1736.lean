/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1736 : Family 9 := level9.get ⟨553,by decide⟩
def sourceMap1736 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1736 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1736_checked : acceptsGraphIso
    (source (graph core1736) (root 9) 0 1) DegreeOneSmallSpectrum1571.graph sourceMap1736=true := by decide +kernel
theorem fusedMap1736_checked : acceptsGraphIso
    (fused (graph core1736) (root 9) 0 1) DegreeOneSmallSpectrum1572.graph fusedMap1736=true := by decide +kernel
theorem certified1736 : Certified (graph core1736) (root 9) 0 1 :=
  of_native_maps core1736 DegreeOneSmallSpectrum1571.graph DegreeOneSmallSpectrum1572.graph
    sourceMap1736 fusedMap1736 sourceMap1736_checked fusedMap1736_checked
    DegreeOneSmallComparisons.comparison1736
#print axioms sourceMap1736_checked
#print axioms fusedMap1736_checked
#print axioms certified1736
def sourceMap1736swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1736swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1736swap_checked : acceptsGraphIso
    (source (graph core1736) (root 9) 1 0) DegreeOneSmallSpectrum1571.graph sourceMap1736swap=true := by decide +kernel
theorem fusedMap1736swap_checked : acceptsGraphIso
    (fused (graph core1736) (root 9) 1 0) DegreeOneSmallSpectrum1572.graph fusedMap1736swap=true := by decide +kernel
theorem certified1736swap : Certified (graph core1736) (root 9) 1 0 :=
  of_native_maps core1736 DegreeOneSmallSpectrum1571.graph DegreeOneSmallSpectrum1572.graph
    sourceMap1736swap fusedMap1736swap sourceMap1736swap_checked fusedMap1736swap_checked
    DegreeOneSmallComparisons.comparison1736
#print axioms sourceMap1736swap_checked
#print axioms fusedMap1736swap_checked
#print axioms certified1736swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
