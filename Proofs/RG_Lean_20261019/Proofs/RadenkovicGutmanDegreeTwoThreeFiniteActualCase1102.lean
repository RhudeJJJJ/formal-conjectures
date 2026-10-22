/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1102 : Family 8 := level8.get ⟨32,by decide⟩
def sourceMap1102 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap1102 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (fusedLabel 8 0 2 v)
theorem sourceMap1102_checked : acceptsGraphIso
    (source (graph core1102) (root 8) 0 2) DegreeOneSmallSpectrum947.graph sourceMap1102=true := by decide +kernel
theorem fusedMap1102_checked : acceptsGraphIso
    (fused (graph core1102) (root 8) 0 2) DegreeOneSmallSpectrum971.graph fusedMap1102=true := by decide +kernel
theorem certified1102 : Certified (graph core1102) (root 8) 0 2 :=
  of_native_maps core1102 DegreeOneSmallSpectrum947.graph DegreeOneSmallSpectrum971.graph
    sourceMap1102 fusedMap1102 sourceMap1102_checked fusedMap1102_checked
    DegreeTwoThreeFiniteComparisons.comparison1102
#print axioms sourceMap1102_checked
#print axioms fusedMap1102_checked
#print axioms certified1102
def sourceMap1102swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,2,3,4,7] (sourceLabel 8 2 0 v)
def fusedMap1102swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (fusedLabel 8 2 0 v)
theorem sourceMap1102swap_checked : acceptsGraphIso
    (source (graph core1102) (root 8) 2 0) DegreeOneSmallSpectrum947.graph sourceMap1102swap=true := by decide +kernel
theorem fusedMap1102swap_checked : acceptsGraphIso
    (fused (graph core1102) (root 8) 2 0) DegreeOneSmallSpectrum971.graph fusedMap1102swap=true := by decide +kernel
theorem certified1102swap : Certified (graph core1102) (root 8) 2 0 :=
  of_native_maps core1102 DegreeOneSmallSpectrum947.graph DegreeOneSmallSpectrum971.graph
    sourceMap1102swap fusedMap1102swap sourceMap1102swap_checked fusedMap1102swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1102
#print axioms sourceMap1102swap_checked
#print axioms fusedMap1102swap_checked
#print axioms certified1102swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
