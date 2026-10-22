/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1143 : Family 8 := level8.get ⟨155,by decide⟩
def sourceMap1143 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1143 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1143_checked : acceptsGraphIso
    (source (graph core1143) (root 8) 0 2) DegreeOneSmallSpectrum1429.graph sourceMap1143=true := by decide +kernel
theorem fusedMap1143_checked : acceptsGraphIso
    (fused (graph core1143) (root 8) 0 2) DegreeOneSmallSpectrum1434.graph fusedMap1143=true := by decide +kernel
theorem certified1143 : Certified (graph core1143) (root 8) 0 2 :=
  of_native_maps core1143 DegreeOneSmallSpectrum1429.graph DegreeOneSmallSpectrum1434.graph
    sourceMap1143 fusedMap1143 sourceMap1143_checked fusedMap1143_checked
    DegreeTwoThreeFiniteComparisons.comparison1143
#print axioms sourceMap1143_checked
#print axioms fusedMap1143_checked
#print axioms certified1143
def sourceMap1143swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1143swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1143swap_checked : acceptsGraphIso
    (source (graph core1143) (root 8) 2 0) DegreeOneSmallSpectrum1429.graph sourceMap1143swap=true := by decide +kernel
theorem fusedMap1143swap_checked : acceptsGraphIso
    (fused (graph core1143) (root 8) 2 0) DegreeOneSmallSpectrum1434.graph fusedMap1143swap=true := by decide +kernel
theorem certified1143swap : Certified (graph core1143) (root 8) 2 0 :=
  of_native_maps core1143 DegreeOneSmallSpectrum1429.graph DegreeOneSmallSpectrum1434.graph
    sourceMap1143swap fusedMap1143swap sourceMap1143swap_checked fusedMap1143swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1143
#print axioms sourceMap1143swap_checked
#print axioms fusedMap1143swap_checked
#print axioms certified1143swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
