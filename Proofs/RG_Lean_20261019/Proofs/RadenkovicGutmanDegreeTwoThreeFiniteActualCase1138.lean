/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1138 : Family 8 := level8.get ⟨143,by decide⟩
def sourceMap1138 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1138 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1138_checked : acceptsGraphIso
    (source (graph core1138) (root 8) 0 2) DegreeOneSmallSpectrum1362.graph sourceMap1138=true := by decide +kernel
theorem fusedMap1138_checked : acceptsGraphIso
    (fused (graph core1138) (root 8) 0 2) DegreeOneSmallSpectrum1364.graph fusedMap1138=true := by decide +kernel
theorem certified1138 : Certified (graph core1138) (root 8) 0 2 :=
  of_native_maps core1138 DegreeOneSmallSpectrum1362.graph DegreeOneSmallSpectrum1364.graph
    sourceMap1138 fusedMap1138 sourceMap1138_checked fusedMap1138_checked
    DegreeTwoThreeFiniteComparisons.comparison1138
#print axioms sourceMap1138_checked
#print axioms fusedMap1138_checked
#print axioms certified1138
def sourceMap1138swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1138swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1138swap_checked : acceptsGraphIso
    (source (graph core1138) (root 8) 2 0) DegreeOneSmallSpectrum1362.graph sourceMap1138swap=true := by decide +kernel
theorem fusedMap1138swap_checked : acceptsGraphIso
    (fused (graph core1138) (root 8) 2 0) DegreeOneSmallSpectrum1364.graph fusedMap1138swap=true := by decide +kernel
theorem certified1138swap : Certified (graph core1138) (root 8) 2 0 :=
  of_native_maps core1138 DegreeOneSmallSpectrum1362.graph DegreeOneSmallSpectrum1364.graph
    sourceMap1138swap fusedMap1138swap sourceMap1138swap_checked fusedMap1138swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1138
#print axioms sourceMap1138swap_checked
#print axioms fusedMap1138swap_checked
#print axioms certified1138swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
