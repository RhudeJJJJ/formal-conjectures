/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1154 : Family 8 := level8.get ⟨179,by decide⟩
def sourceMap1154 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1154 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1154_checked : acceptsGraphIso
    (source (graph core1154) (root 8) 0 2) DegreeOneSmallSpectrum1511.graph sourceMap1154=true := by decide +kernel
theorem fusedMap1154_checked : acceptsGraphIso
    (fused (graph core1154) (root 8) 0 2) DegreeOneSmallSpectrum1508.graph fusedMap1154=true := by decide +kernel
theorem certified1154 : Certified (graph core1154) (root 8) 0 2 :=
  of_native_maps core1154 DegreeOneSmallSpectrum1511.graph DegreeOneSmallSpectrum1508.graph
    sourceMap1154 fusedMap1154 sourceMap1154_checked fusedMap1154_checked
    DegreeTwoThreeFiniteComparisons.comparison1154
#print axioms sourceMap1154_checked
#print axioms fusedMap1154_checked
#print axioms certified1154
def sourceMap1154swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1154swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1154swap_checked : acceptsGraphIso
    (source (graph core1154) (root 8) 2 0) DegreeOneSmallSpectrum1511.graph sourceMap1154swap=true := by decide +kernel
theorem fusedMap1154swap_checked : acceptsGraphIso
    (fused (graph core1154) (root 8) 2 0) DegreeOneSmallSpectrum1508.graph fusedMap1154swap=true := by decide +kernel
theorem certified1154swap : Certified (graph core1154) (root 8) 2 0 :=
  of_native_maps core1154 DegreeOneSmallSpectrum1511.graph DegreeOneSmallSpectrum1508.graph
    sourceMap1154swap fusedMap1154swap sourceMap1154swap_checked fusedMap1154swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1154
#print axioms sourceMap1154swap_checked
#print axioms fusedMap1154swap_checked
#print axioms certified1154swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
