/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1170 : Family 8 := level8.get ⟨216,by decide⟩
def sourceMap1170 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1170 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1170_checked : acceptsGraphIso
    (source (graph core1170) (root 8) 0 2) DegreeOneSmallSpectrum1809.graph sourceMap1170=true := by decide +kernel
theorem fusedMap1170_checked : acceptsGraphIso
    (fused (graph core1170) (root 8) 0 2) DegreeOneSmallSpectrum1119.graph fusedMap1170=true := by decide +kernel
theorem certified1170 : Certified (graph core1170) (root 8) 0 2 :=
  of_native_maps core1170 DegreeOneSmallSpectrum1809.graph DegreeOneSmallSpectrum1119.graph
    sourceMap1170 fusedMap1170 sourceMap1170_checked fusedMap1170_checked
    DegreeTwoThreeFiniteComparisons.comparison1170
#print axioms sourceMap1170_checked
#print axioms fusedMap1170_checked
#print axioms certified1170
def sourceMap1170swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1170swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1170swap_checked : acceptsGraphIso
    (source (graph core1170) (root 8) 2 0) DegreeOneSmallSpectrum1809.graph sourceMap1170swap=true := by decide +kernel
theorem fusedMap1170swap_checked : acceptsGraphIso
    (fused (graph core1170) (root 8) 2 0) DegreeOneSmallSpectrum1119.graph fusedMap1170swap=true := by decide +kernel
theorem certified1170swap : Certified (graph core1170) (root 8) 2 0 :=
  of_native_maps core1170 DegreeOneSmallSpectrum1809.graph DegreeOneSmallSpectrum1119.graph
    sourceMap1170swap fusedMap1170swap sourceMap1170swap_checked fusedMap1170swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1170
#print axioms sourceMap1170swap_checked
#print axioms fusedMap1170swap_checked
#print axioms certified1170swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
