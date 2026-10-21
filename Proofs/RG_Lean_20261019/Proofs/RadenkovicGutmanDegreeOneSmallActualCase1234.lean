/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1234 : Family 9 := level9.get ⟨21,by decide⟩
def sourceMap1234 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1234 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1234_checked : acceptsGraphIso
    (source (graph core1234) (root 9) 0 1) DegreeOneSmallSpectrum926.graph sourceMap1234=true := by decide +kernel
theorem fusedMap1234_checked : acceptsGraphIso
    (fused (graph core1234) (root 9) 0 1) DegreeOneSmallSpectrum943.graph fusedMap1234=true := by decide +kernel
theorem certified1234 : Certified (graph core1234) (root 9) 0 1 :=
  of_native_maps core1234 DegreeOneSmallSpectrum926.graph DegreeOneSmallSpectrum943.graph
    sourceMap1234 fusedMap1234 sourceMap1234_checked fusedMap1234_checked
    DegreeOneSmallComparisons.comparison1234
#print axioms sourceMap1234_checked
#print axioms fusedMap1234_checked
#print axioms certified1234
def sourceMap1234swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1234swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1234swap_checked : acceptsGraphIso
    (source (graph core1234) (root 9) 1 0) DegreeOneSmallSpectrum926.graph sourceMap1234swap=true := by decide +kernel
theorem fusedMap1234swap_checked : acceptsGraphIso
    (fused (graph core1234) (root 9) 1 0) DegreeOneSmallSpectrum943.graph fusedMap1234swap=true := by decide +kernel
theorem certified1234swap : Certified (graph core1234) (root 9) 1 0 :=
  of_native_maps core1234 DegreeOneSmallSpectrum926.graph DegreeOneSmallSpectrum943.graph
    sourceMap1234swap fusedMap1234swap sourceMap1234swap_checked fusedMap1234swap_checked
    DegreeOneSmallComparisons.comparison1234
#print axioms sourceMap1234swap_checked
#print axioms fusedMap1234swap_checked
#print axioms certified1234swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
