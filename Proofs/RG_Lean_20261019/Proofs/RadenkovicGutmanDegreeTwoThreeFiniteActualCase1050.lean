/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1050 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap1050 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7] (sourceLabel 6 0 2 v)
def fusedMap1050 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1050_checked : acceptsGraphIso
    (source (graph core1050) (root 6) 0 2) DegreeOneSmallSpectrum314.graph sourceMap1050=true := by decide +kernel
theorem fusedMap1050_checked : acceptsGraphIso
    (fused (graph core1050) (root 6) 0 2) DegreeOneSmallSpectrum183.graph fusedMap1050=true := by decide +kernel
theorem certified1050 : Certified (graph core1050) (root 6) 0 2 :=
  of_native_maps core1050 DegreeOneSmallSpectrum314.graph DegreeOneSmallSpectrum183.graph
    sourceMap1050 fusedMap1050 sourceMap1050_checked fusedMap1050_checked
    DegreeTwoThreeFiniteComparisons.comparison1050
#print axioms sourceMap1050_checked
#print axioms fusedMap1050_checked
#print axioms certified1050
def sourceMap1050swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,5,6,7,10] (sourceLabel 6 2 0 v)
def fusedMap1050swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1050swap_checked : acceptsGraphIso
    (source (graph core1050) (root 6) 2 0) DegreeOneSmallSpectrum314.graph sourceMap1050swap=true := by decide +kernel
theorem fusedMap1050swap_checked : acceptsGraphIso
    (fused (graph core1050) (root 6) 2 0) DegreeOneSmallSpectrum183.graph fusedMap1050swap=true := by decide +kernel
theorem certified1050swap : Certified (graph core1050) (root 6) 2 0 :=
  of_native_maps core1050 DegreeOneSmallSpectrum314.graph DegreeOneSmallSpectrum183.graph
    sourceMap1050swap fusedMap1050swap sourceMap1050swap_checked fusedMap1050swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1050
#print axioms sourceMap1050swap_checked
#print axioms fusedMap1050swap_checked
#print axioms certified1050swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
