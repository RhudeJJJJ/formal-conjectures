/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1097 : Family 8 := level8.get ⟨13,by decide⟩
def sourceMap1097 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1097 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1097_checked : acceptsGraphIso
    (source (graph core1097) (root 8) 0 2) DegreeOneSmallSpectrum902.graph sourceMap1097=true := by decide +kernel
theorem fusedMap1097_checked : acceptsGraphIso
    (fused (graph core1097) (root 8) 0 2) DegreeOneSmallSpectrum907.graph fusedMap1097=true := by decide +kernel
theorem certified1097 : Certified (graph core1097) (root 8) 0 2 :=
  of_native_maps core1097 DegreeOneSmallSpectrum902.graph DegreeOneSmallSpectrum907.graph
    sourceMap1097 fusedMap1097 sourceMap1097_checked fusedMap1097_checked
    DegreeTwoThreeFiniteComparisons.comparison1097
#print axioms sourceMap1097_checked
#print axioms fusedMap1097_checked
#print axioms certified1097
def sourceMap1097swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1097swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1097swap_checked : acceptsGraphIso
    (source (graph core1097) (root 8) 2 0) DegreeOneSmallSpectrum902.graph sourceMap1097swap=true := by decide +kernel
theorem fusedMap1097swap_checked : acceptsGraphIso
    (fused (graph core1097) (root 8) 2 0) DegreeOneSmallSpectrum907.graph fusedMap1097swap=true := by decide +kernel
theorem certified1097swap : Certified (graph core1097) (root 8) 2 0 :=
  of_native_maps core1097 DegreeOneSmallSpectrum902.graph DegreeOneSmallSpectrum907.graph
    sourceMap1097swap fusedMap1097swap sourceMap1097swap_checked fusedMap1097swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1097
#print axioms sourceMap1097swap_checked
#print axioms fusedMap1097swap_checked
#print axioms certified1097swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
