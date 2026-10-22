/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1113 : Family 8 := level8.get ⟨74,by decide⟩
def sourceMap1113 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1113 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1113_checked : acceptsGraphIso
    (source (graph core1113) (root 8) 0 2) DegreeOneSmallSpectrum1488.graph sourceMap1113=true := by decide +kernel
theorem fusedMap1113_checked : acceptsGraphIso
    (fused (graph core1113) (root 8) 0 2) DegreeOneSmallSpectrum950.graph fusedMap1113=true := by decide +kernel
theorem certified1113 : Certified (graph core1113) (root 8) 0 2 :=
  of_native_maps core1113 DegreeOneSmallSpectrum1488.graph DegreeOneSmallSpectrum950.graph
    sourceMap1113 fusedMap1113 sourceMap1113_checked fusedMap1113_checked
    DegreeTwoThreeFiniteComparisons.comparison1113
#print axioms sourceMap1113_checked
#print axioms fusedMap1113_checked
#print axioms certified1113
def sourceMap1113swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1113swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1113swap_checked : acceptsGraphIso
    (source (graph core1113) (root 8) 2 0) DegreeOneSmallSpectrum1488.graph sourceMap1113swap=true := by decide +kernel
theorem fusedMap1113swap_checked : acceptsGraphIso
    (fused (graph core1113) (root 8) 2 0) DegreeOneSmallSpectrum950.graph fusedMap1113swap=true := by decide +kernel
theorem certified1113swap : Certified (graph core1113) (root 8) 2 0 :=
  of_native_maps core1113 DegreeOneSmallSpectrum1488.graph DegreeOneSmallSpectrum950.graph
    sourceMap1113swap fusedMap1113swap sourceMap1113swap_checked fusedMap1113swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1113
#print axioms sourceMap1113swap_checked
#print axioms fusedMap1113swap_checked
#print axioms certified1113swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
