/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5056 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5056 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,5,6,7,2,3,4,0,8,9,10,11] (sourceLabel 3 2 4 v)
def fusedMap5056 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 2 4 v)
theorem sourceMap5056_checked : acceptsGraphIso
    (source (graph core5056) (root 3) 2 4) DegreeOneSmallSpectrum571.graph sourceMap5056=true := by decide +kernel
theorem fusedMap5056_checked : acceptsGraphIso
    (fused (graph core5056) (root 3) 2 4) DegreeOneSmallSpectrum386.graph fusedMap5056=true := by decide +kernel
theorem certified5056 : Certified (graph core5056) (root 3) 2 4 :=
  of_native_maps core5056 DegreeOneSmallSpectrum571.graph DegreeOneSmallSpectrum386.graph
    sourceMap5056 fusedMap5056 sourceMap5056_checked fusedMap5056_checked
    DegreeTwoThreeFiniteComparisons.comparison5056
#print axioms sourceMap5056_checked
#print axioms fusedMap5056_checked
#print axioms certified5056
def sourceMap5056swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,5,6,7,0,8,9,10,11,2,3,4] (sourceLabel 3 4 2 v)
def fusedMap5056swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 4 2 v)
theorem sourceMap5056swap_checked : acceptsGraphIso
    (source (graph core5056) (root 3) 4 2) DegreeOneSmallSpectrum571.graph sourceMap5056swap=true := by decide +kernel
theorem fusedMap5056swap_checked : acceptsGraphIso
    (fused (graph core5056) (root 3) 4 2) DegreeOneSmallSpectrum386.graph fusedMap5056swap=true := by decide +kernel
theorem certified5056swap : Certified (graph core5056) (root 3) 4 2 :=
  of_native_maps core5056 DegreeOneSmallSpectrum571.graph DegreeOneSmallSpectrum386.graph
    sourceMap5056swap fusedMap5056swap sourceMap5056swap_checked fusedMap5056swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5056
#print axioms sourceMap5056swap_checked
#print axioms fusedMap5056swap_checked
#print axioms certified5056swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
