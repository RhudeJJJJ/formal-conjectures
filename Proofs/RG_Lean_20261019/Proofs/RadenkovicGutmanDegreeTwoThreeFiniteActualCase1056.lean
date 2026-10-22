/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1056 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap1056 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap1056 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1056_checked : acceptsGraphIso
    (source (graph core1056) (root 6) 0 2) DegreeOneSmallSpectrum236.graph sourceMap1056=true := by decide +kernel
theorem fusedMap1056_checked : acceptsGraphIso
    (fused (graph core1056) (root 6) 0 2) DegreeOneSmallSpectrum239.graph fusedMap1056=true := by decide +kernel
theorem certified1056 : Certified (graph core1056) (root 6) 0 2 :=
  of_native_maps core1056 DegreeOneSmallSpectrum236.graph DegreeOneSmallSpectrum239.graph
    sourceMap1056 fusedMap1056 sourceMap1056_checked fusedMap1056_checked
    DegreeTwoThreeFiniteComparisons.comparison1056
#print axioms sourceMap1056_checked
#print axioms fusedMap1056_checked
#print axioms certified1056
def sourceMap1056swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap1056swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1056swap_checked : acceptsGraphIso
    (source (graph core1056) (root 6) 2 0) DegreeOneSmallSpectrum236.graph sourceMap1056swap=true := by decide +kernel
theorem fusedMap1056swap_checked : acceptsGraphIso
    (fused (graph core1056) (root 6) 2 0) DegreeOneSmallSpectrum239.graph fusedMap1056swap=true := by decide +kernel
theorem certified1056swap : Certified (graph core1056) (root 6) 2 0 :=
  of_native_maps core1056 DegreeOneSmallSpectrum236.graph DegreeOneSmallSpectrum239.graph
    sourceMap1056swap fusedMap1056swap sourceMap1056swap_checked fusedMap1056swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1056
#print axioms sourceMap1056swap_checked
#print axioms fusedMap1056swap_checked
#print axioms certified1056swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
