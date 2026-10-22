/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1160 : Family 8 := level8.get ⟨194,by decide⟩
def sourceMap1160 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1160 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1160_checked : acceptsGraphIso
    (source (graph core1160) (root 8) 0 2) DegreeOneSmallSpectrum1599.graph sourceMap1160=true := by decide +kernel
theorem fusedMap1160_checked : acceptsGraphIso
    (fused (graph core1160) (root 8) 0 2) DegreeOneSmallSpectrum993.graph fusedMap1160=true := by decide +kernel
theorem certified1160 : Certified (graph core1160) (root 8) 0 2 :=
  of_native_maps core1160 DegreeOneSmallSpectrum1599.graph DegreeOneSmallSpectrum993.graph
    sourceMap1160 fusedMap1160 sourceMap1160_checked fusedMap1160_checked
    DegreeTwoThreeFiniteComparisons.comparison1160
#print axioms sourceMap1160_checked
#print axioms fusedMap1160_checked
#print axioms certified1160
def sourceMap1160swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1160swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1160swap_checked : acceptsGraphIso
    (source (graph core1160) (root 8) 2 0) DegreeOneSmallSpectrum1599.graph sourceMap1160swap=true := by decide +kernel
theorem fusedMap1160swap_checked : acceptsGraphIso
    (fused (graph core1160) (root 8) 2 0) DegreeOneSmallSpectrum993.graph fusedMap1160swap=true := by decide +kernel
theorem certified1160swap : Certified (graph core1160) (root 8) 2 0 :=
  of_native_maps core1160 DegreeOneSmallSpectrum1599.graph DegreeOneSmallSpectrum993.graph
    sourceMap1160swap fusedMap1160swap sourceMap1160swap_checked fusedMap1160swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1160
#print axioms sourceMap1160swap_checked
#print axioms fusedMap1160swap_checked
#print axioms certified1160swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
