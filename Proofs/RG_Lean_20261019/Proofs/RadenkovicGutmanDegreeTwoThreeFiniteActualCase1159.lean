/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1159 : Family 8 := level8.get ⟨193,by decide⟩
def sourceMap1159 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1159 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1159_checked : acceptsGraphIso
    (source (graph core1159) (root 8) 0 2) DegreeOneSmallSpectrum1585.graph sourceMap1159=true := by decide +kernel
theorem fusedMap1159_checked : acceptsGraphIso
    (fused (graph core1159) (root 8) 0 2) DegreeOneSmallSpectrum988.graph fusedMap1159=true := by decide +kernel
theorem certified1159 : Certified (graph core1159) (root 8) 0 2 :=
  of_native_maps core1159 DegreeOneSmallSpectrum1585.graph DegreeOneSmallSpectrum988.graph
    sourceMap1159 fusedMap1159 sourceMap1159_checked fusedMap1159_checked
    DegreeTwoThreeFiniteComparisons.comparison1159
#print axioms sourceMap1159_checked
#print axioms fusedMap1159_checked
#print axioms certified1159
def sourceMap1159swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1159swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1159swap_checked : acceptsGraphIso
    (source (graph core1159) (root 8) 2 0) DegreeOneSmallSpectrum1585.graph sourceMap1159swap=true := by decide +kernel
theorem fusedMap1159swap_checked : acceptsGraphIso
    (fused (graph core1159) (root 8) 2 0) DegreeOneSmallSpectrum988.graph fusedMap1159swap=true := by decide +kernel
theorem certified1159swap : Certified (graph core1159) (root 8) 2 0 :=
  of_native_maps core1159 DegreeOneSmallSpectrum1585.graph DegreeOneSmallSpectrum988.graph
    sourceMap1159swap fusedMap1159swap sourceMap1159swap_checked fusedMap1159swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1159
#print axioms sourceMap1159swap_checked
#print axioms fusedMap1159swap_checked
#print axioms certified1159swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
