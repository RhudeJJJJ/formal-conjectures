/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1124 : Family 8 := level8.get ⟨105,by decide⟩
def sourceMap1124 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1124 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1124_checked : acceptsGraphIso
    (source (graph core1124) (root 8) 0 2) DegreeOneSmallSpectrum1057.graph sourceMap1124=true := by decide +kernel
theorem fusedMap1124_checked : acceptsGraphIso
    (fused (graph core1124) (root 8) 0 2) DegreeOneSmallSpectrum1059.graph fusedMap1124=true := by decide +kernel
theorem certified1124 : Certified (graph core1124) (root 8) 0 2 :=
  of_native_maps core1124 DegreeOneSmallSpectrum1057.graph DegreeOneSmallSpectrum1059.graph
    sourceMap1124 fusedMap1124 sourceMap1124_checked fusedMap1124_checked
    DegreeTwoThreeFiniteComparisons.comparison1124
#print axioms sourceMap1124_checked
#print axioms fusedMap1124_checked
#print axioms certified1124
def sourceMap1124swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1124swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1124swap_checked : acceptsGraphIso
    (source (graph core1124) (root 8) 2 0) DegreeOneSmallSpectrum1057.graph sourceMap1124swap=true := by decide +kernel
theorem fusedMap1124swap_checked : acceptsGraphIso
    (fused (graph core1124) (root 8) 2 0) DegreeOneSmallSpectrum1059.graph fusedMap1124swap=true := by decide +kernel
theorem certified1124swap : Certified (graph core1124) (root 8) 2 0 :=
  of_native_maps core1124 DegreeOneSmallSpectrum1057.graph DegreeOneSmallSpectrum1059.graph
    sourceMap1124swap fusedMap1124swap sourceMap1124swap_checked fusedMap1124swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1124
#print axioms sourceMap1124swap_checked
#print axioms fusedMap1124swap_checked
#print axioms certified1124swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
