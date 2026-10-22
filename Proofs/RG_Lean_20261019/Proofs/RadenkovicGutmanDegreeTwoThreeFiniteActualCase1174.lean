/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1174 : Family 8 := level8.get ⟨223,by decide⟩
def sourceMap1174 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1174 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1174_checked : acceptsGraphIso
    (source (graph core1174) (root 8) 0 2) DegreeOneSmallSpectrum1870.graph sourceMap1174=true := by decide +kernel
theorem fusedMap1174_checked : acceptsGraphIso
    (fused (graph core1174) (root 8) 0 2) DegreeOneSmallSpectrum1184.graph fusedMap1174=true := by decide +kernel
theorem certified1174 : Certified (graph core1174) (root 8) 0 2 :=
  of_native_maps core1174 DegreeOneSmallSpectrum1870.graph DegreeOneSmallSpectrum1184.graph
    sourceMap1174 fusedMap1174 sourceMap1174_checked fusedMap1174_checked
    DegreeTwoThreeFiniteComparisons.comparison1174
#print axioms sourceMap1174_checked
#print axioms fusedMap1174_checked
#print axioms certified1174
def sourceMap1174swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1174swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1174swap_checked : acceptsGraphIso
    (source (graph core1174) (root 8) 2 0) DegreeOneSmallSpectrum1870.graph sourceMap1174swap=true := by decide +kernel
theorem fusedMap1174swap_checked : acceptsGraphIso
    (fused (graph core1174) (root 8) 2 0) DegreeOneSmallSpectrum1184.graph fusedMap1174swap=true := by decide +kernel
theorem certified1174swap : Certified (graph core1174) (root 8) 2 0 :=
  of_native_maps core1174 DegreeOneSmallSpectrum1870.graph DegreeOneSmallSpectrum1184.graph
    sourceMap1174swap fusedMap1174swap sourceMap1174swap_checked fusedMap1174swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1174
#print axioms sourceMap1174swap_checked
#print axioms fusedMap1174swap_checked
#print axioms certified1174swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
