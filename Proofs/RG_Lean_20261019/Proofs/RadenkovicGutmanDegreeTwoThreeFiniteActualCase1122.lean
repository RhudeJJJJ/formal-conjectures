/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1122 : Family 8 := level8.get ⟨98,by decide⟩
def sourceMap1122 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1122 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1122_checked : acceptsGraphIso
    (source (graph core1122) (root 8) 0 2) DegreeOneSmallSpectrum1006.graph sourceMap1122=true := by decide +kernel
theorem fusedMap1122_checked : acceptsGraphIso
    (fused (graph core1122) (root 8) 0 2) DegreeOneSmallSpectrum1008.graph fusedMap1122=true := by decide +kernel
theorem certified1122 : Certified (graph core1122) (root 8) 0 2 :=
  of_native_maps core1122 DegreeOneSmallSpectrum1006.graph DegreeOneSmallSpectrum1008.graph
    sourceMap1122 fusedMap1122 sourceMap1122_checked fusedMap1122_checked
    DegreeTwoThreeFiniteComparisons.comparison1122
#print axioms sourceMap1122_checked
#print axioms fusedMap1122_checked
#print axioms certified1122
def sourceMap1122swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1122swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1122swap_checked : acceptsGraphIso
    (source (graph core1122) (root 8) 2 0) DegreeOneSmallSpectrum1006.graph sourceMap1122swap=true := by decide +kernel
theorem fusedMap1122swap_checked : acceptsGraphIso
    (fused (graph core1122) (root 8) 2 0) DegreeOneSmallSpectrum1008.graph fusedMap1122swap=true := by decide +kernel
theorem certified1122swap : Certified (graph core1122) (root 8) 2 0 :=
  of_native_maps core1122 DegreeOneSmallSpectrum1006.graph DegreeOneSmallSpectrum1008.graph
    sourceMap1122swap fusedMap1122swap sourceMap1122swap_checked fusedMap1122swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1122
#print axioms sourceMap1122swap_checked
#print axioms fusedMap1122swap_checked
#print axioms certified1122swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
