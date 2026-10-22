/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1098 : Family 8 := level8.get ⟨19,by decide⟩
def sourceMap1098 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1098 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1098_checked : acceptsGraphIso
    (source (graph core1098) (root 8) 0 2) DegreeOneSmallSpectrum938.graph sourceMap1098=true := by decide +kernel
theorem fusedMap1098_checked : acceptsGraphIso
    (fused (graph core1098) (root 8) 0 2) DegreeOneSmallSpectrum943.graph fusedMap1098=true := by decide +kernel
theorem certified1098 : Certified (graph core1098) (root 8) 0 2 :=
  of_native_maps core1098 DegreeOneSmallSpectrum938.graph DegreeOneSmallSpectrum943.graph
    sourceMap1098 fusedMap1098 sourceMap1098_checked fusedMap1098_checked
    DegreeTwoThreeFiniteComparisons.comparison1098
#print axioms sourceMap1098_checked
#print axioms fusedMap1098_checked
#print axioms certified1098
def sourceMap1098swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1098swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1098swap_checked : acceptsGraphIso
    (source (graph core1098) (root 8) 2 0) DegreeOneSmallSpectrum938.graph sourceMap1098swap=true := by decide +kernel
theorem fusedMap1098swap_checked : acceptsGraphIso
    (fused (graph core1098) (root 8) 2 0) DegreeOneSmallSpectrum943.graph fusedMap1098swap=true := by decide +kernel
theorem certified1098swap : Certified (graph core1098) (root 8) 2 0 :=
  of_native_maps core1098 DegreeOneSmallSpectrum938.graph DegreeOneSmallSpectrum943.graph
    sourceMap1098swap fusedMap1098swap sourceMap1098swap_checked fusedMap1098swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1098
#print axioms sourceMap1098swap_checked
#print axioms fusedMap1098swap_checked
#print axioms certified1098swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
