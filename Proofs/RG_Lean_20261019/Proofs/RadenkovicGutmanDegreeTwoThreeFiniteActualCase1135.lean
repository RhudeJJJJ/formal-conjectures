/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1135 : Family 8 := level8.get ⟨135,by decide⟩
def sourceMap1135 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1135 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1135_checked : acceptsGraphIso
    (source (graph core1135) (root 8) 0 2) DegreeOneSmallSpectrum1311.graph sourceMap1135=true := by decide +kernel
theorem fusedMap1135_checked : acceptsGraphIso
    (fused (graph core1135) (root 8) 0 2) DegreeOneSmallSpectrum1313.graph fusedMap1135=true := by decide +kernel
theorem certified1135 : Certified (graph core1135) (root 8) 0 2 :=
  of_native_maps core1135 DegreeOneSmallSpectrum1311.graph DegreeOneSmallSpectrum1313.graph
    sourceMap1135 fusedMap1135 sourceMap1135_checked fusedMap1135_checked
    DegreeTwoThreeFiniteComparisons.comparison1135
#print axioms sourceMap1135_checked
#print axioms fusedMap1135_checked
#print axioms certified1135
def sourceMap1135swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1135swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1135swap_checked : acceptsGraphIso
    (source (graph core1135) (root 8) 2 0) DegreeOneSmallSpectrum1311.graph sourceMap1135swap=true := by decide +kernel
theorem fusedMap1135swap_checked : acceptsGraphIso
    (fused (graph core1135) (root 8) 2 0) DegreeOneSmallSpectrum1313.graph fusedMap1135swap=true := by decide +kernel
theorem certified1135swap : Certified (graph core1135) (root 8) 2 0 :=
  of_native_maps core1135 DegreeOneSmallSpectrum1311.graph DegreeOneSmallSpectrum1313.graph
    sourceMap1135swap fusedMap1135swap sourceMap1135swap_checked fusedMap1135swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1135
#print axioms sourceMap1135swap_checked
#print axioms fusedMap1135swap_checked
#print axioms certified1135swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
