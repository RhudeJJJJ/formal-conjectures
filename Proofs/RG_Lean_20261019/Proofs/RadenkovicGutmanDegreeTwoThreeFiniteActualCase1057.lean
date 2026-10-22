/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1057 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap1057 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap1057 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1057_checked : acceptsGraphIso
    (source (graph core1057) (root 6) 0 2) DegreeOneSmallSpectrum246.graph sourceMap1057=true := by decide +kernel
theorem fusedMap1057_checked : acceptsGraphIso
    (fused (graph core1057) (root 6) 0 2) DegreeOneSmallSpectrum249.graph fusedMap1057=true := by decide +kernel
theorem certified1057 : Certified (graph core1057) (root 6) 0 2 :=
  of_native_maps core1057 DegreeOneSmallSpectrum246.graph DegreeOneSmallSpectrum249.graph
    sourceMap1057 fusedMap1057 sourceMap1057_checked fusedMap1057_checked
    DegreeTwoThreeFiniteComparisons.comparison1057
#print axioms sourceMap1057_checked
#print axioms fusedMap1057_checked
#print axioms certified1057
def sourceMap1057swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap1057swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1057swap_checked : acceptsGraphIso
    (source (graph core1057) (root 6) 2 0) DegreeOneSmallSpectrum246.graph sourceMap1057swap=true := by decide +kernel
theorem fusedMap1057swap_checked : acceptsGraphIso
    (fused (graph core1057) (root 6) 2 0) DegreeOneSmallSpectrum249.graph fusedMap1057swap=true := by decide +kernel
theorem certified1057swap : Certified (graph core1057) (root 6) 2 0 :=
  of_native_maps core1057 DegreeOneSmallSpectrum246.graph DegreeOneSmallSpectrum249.graph
    sourceMap1057swap fusedMap1057swap sourceMap1057swap_checked fusedMap1057swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1057
#print axioms sourceMap1057swap_checked
#print axioms fusedMap1057swap_checked
#print axioms certified1057swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
