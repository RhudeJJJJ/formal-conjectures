/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1738 : Family 9 := level9.get ⟨561,by decide⟩
def sourceMap1738 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1738 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1738_checked : acceptsGraphIso
    (source (graph core1738) (root 9) 0 1) DegreeOneSmallSpectrum1603.graph sourceMap1738=true := by decide +kernel
theorem fusedMap1738_checked : acceptsGraphIso
    (fused (graph core1738) (root 9) 0 1) DegreeOneSmallSpectrum1604.graph fusedMap1738=true := by decide +kernel
theorem certified1738 : Certified (graph core1738) (root 9) 0 1 :=
  of_native_maps core1738 DegreeOneSmallSpectrum1603.graph DegreeOneSmallSpectrum1604.graph
    sourceMap1738 fusedMap1738 sourceMap1738_checked fusedMap1738_checked
    DegreeOneSmallComparisons.comparison1738
#print axioms sourceMap1738_checked
#print axioms fusedMap1738_checked
#print axioms certified1738
def sourceMap1738swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1738swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1738swap_checked : acceptsGraphIso
    (source (graph core1738) (root 9) 1 0) DegreeOneSmallSpectrum1603.graph sourceMap1738swap=true := by decide +kernel
theorem fusedMap1738swap_checked : acceptsGraphIso
    (fused (graph core1738) (root 9) 1 0) DegreeOneSmallSpectrum1604.graph fusedMap1738swap=true := by decide +kernel
theorem certified1738swap : Certified (graph core1738) (root 9) 1 0 :=
  of_native_maps core1738 DegreeOneSmallSpectrum1603.graph DegreeOneSmallSpectrum1604.graph
    sourceMap1738swap fusedMap1738swap sourceMap1738swap_checked fusedMap1738swap_checked
    DegreeOneSmallComparisons.comparison1738
#print axioms sourceMap1738swap_checked
#print axioms fusedMap1738swap_checked
#print axioms certified1738swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
