/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1038 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap1038 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,8,9,5,6,7] (sourceLabel 5 0 2 v)
def fusedMap1038 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap1038_checked : acceptsGraphIso
    (source (graph core1038) (root 5) 0 2) DegreeOneSmallSpectrum129.graph sourceMap1038=true := by decide +kernel
theorem fusedMap1038_checked : acceptsGraphIso
    (fused (graph core1038) (root 5) 0 2) DegreeOneSmallSpectrum076.graph fusedMap1038=true := by decide +kernel
theorem certified1038 : Certified (graph core1038) (root 5) 0 2 :=
  of_native_maps core1038 DegreeOneSmallSpectrum129.graph DegreeOneSmallSpectrum076.graph
    sourceMap1038 fusedMap1038 sourceMap1038_checked fusedMap1038_checked
    DegreeTwoThreeFiniteComparisons.comparison1038
#print axioms sourceMap1038_checked
#print axioms fusedMap1038_checked
#print axioms certified1038
def sourceMap1038swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,8,5,6,7,9] (sourceLabel 5 2 0 v)
def fusedMap1038swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap1038swap_checked : acceptsGraphIso
    (source (graph core1038) (root 5) 2 0) DegreeOneSmallSpectrum129.graph sourceMap1038swap=true := by decide +kernel
theorem fusedMap1038swap_checked : acceptsGraphIso
    (fused (graph core1038) (root 5) 2 0) DegreeOneSmallSpectrum076.graph fusedMap1038swap=true := by decide +kernel
theorem certified1038swap : Certified (graph core1038) (root 5) 2 0 :=
  of_native_maps core1038 DegreeOneSmallSpectrum129.graph DegreeOneSmallSpectrum076.graph
    sourceMap1038swap fusedMap1038swap sourceMap1038swap_checked fusedMap1038swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1038
#print axioms sourceMap1038swap_checked
#print axioms fusedMap1038swap_checked
#print axioms certified1038swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
