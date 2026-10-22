/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2056 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap2056 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (sourceLabel 3 0 4 v)
def fusedMap2056 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 0 4 v)
theorem sourceMap2056_checked : acceptsGraphIso
    (source (graph core2056) (root 3) 0 4) DegreeOneSmallSpectrum082.graph sourceMap2056=true := by decide +kernel
theorem fusedMap2056_checked : acceptsGraphIso
    (fused (graph core2056) (root 3) 0 4) DegreeOneSmallSpectrum086.graph fusedMap2056=true := by decide +kernel
theorem certified2056 : Certified (graph core2056) (root 3) 0 4 :=
  of_native_maps core2056 DegreeOneSmallSpectrum082.graph DegreeOneSmallSpectrum086.graph
    sourceMap2056 fusedMap2056 sourceMap2056_checked fusedMap2056_checked
    DegreeTwoThreeFiniteComparisons.comparison2056
#print axioms sourceMap2056_checked
#print axioms fusedMap2056_checked
#print axioms certified2056
def sourceMap2056swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,2,3,4,0,6,7,8,9,5] (sourceLabel 3 4 0 v)
def fusedMap2056swap : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 4 0 v)
theorem sourceMap2056swap_checked : acceptsGraphIso
    (source (graph core2056) (root 3) 4 0) DegreeOneSmallSpectrum082.graph sourceMap2056swap=true := by decide +kernel
theorem fusedMap2056swap_checked : acceptsGraphIso
    (fused (graph core2056) (root 3) 4 0) DegreeOneSmallSpectrum086.graph fusedMap2056swap=true := by decide +kernel
theorem certified2056swap : Certified (graph core2056) (root 3) 4 0 :=
  of_native_maps core2056 DegreeOneSmallSpectrum082.graph DegreeOneSmallSpectrum086.graph
    sourceMap2056swap fusedMap2056swap sourceMap2056swap_checked fusedMap2056swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2056
#print axioms sourceMap2056swap_checked
#print axioms fusedMap2056swap_checked
#print axioms certified2056swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
