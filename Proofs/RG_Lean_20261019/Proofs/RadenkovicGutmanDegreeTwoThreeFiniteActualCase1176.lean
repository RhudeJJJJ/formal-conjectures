/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1176 : Family 8 := level8.get ⟨231,by decide⟩
def sourceMap1176 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1176 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1176_checked : acceptsGraphIso
    (source (graph core1176) (root 8) 0 2) DegreeOneSmallSpectrum1897.graph sourceMap1176=true := by decide +kernel
theorem fusedMap1176_checked : acceptsGraphIso
    (fused (graph core1176) (root 8) 0 2) DegreeOneSmallSpectrum1293.graph fusedMap1176=true := by decide +kernel
theorem certified1176 : Certified (graph core1176) (root 8) 0 2 :=
  of_native_maps core1176 DegreeOneSmallSpectrum1897.graph DegreeOneSmallSpectrum1293.graph
    sourceMap1176 fusedMap1176 sourceMap1176_checked fusedMap1176_checked
    DegreeTwoThreeFiniteComparisons.comparison1176
#print axioms sourceMap1176_checked
#print axioms fusedMap1176_checked
#print axioms certified1176
def sourceMap1176swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1176swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1176swap_checked : acceptsGraphIso
    (source (graph core1176) (root 8) 2 0) DegreeOneSmallSpectrum1897.graph sourceMap1176swap=true := by decide +kernel
theorem fusedMap1176swap_checked : acceptsGraphIso
    (fused (graph core1176) (root 8) 2 0) DegreeOneSmallSpectrum1293.graph fusedMap1176swap=true := by decide +kernel
theorem certified1176swap : Certified (graph core1176) (root 8) 2 0 :=
  of_native_maps core1176 DegreeOneSmallSpectrum1897.graph DegreeOneSmallSpectrum1293.graph
    sourceMap1176swap fusedMap1176swap sourceMap1176swap_checked fusedMap1176swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1176
#print axioms sourceMap1176swap_checked
#print axioms fusedMap1176swap_checked
#print axioms certified1176swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
