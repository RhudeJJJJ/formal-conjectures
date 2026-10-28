/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5477 : Family 6 := level6.get ⟨35,by decide⟩
def sourceMap5477 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap5477 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap5477_checked : acceptsGraphIso
    (source (graph core5477) (root 6) 0 4) DegreeOneSmallSpectrum1481.graph sourceMap5477=true := by decide +kernel
theorem fusedMap5477_checked : acceptsGraphIso
    (fused (graph core5477) (root 6) 0 4) DegreeOneSmallSpectrum947.graph fusedMap5477=true := by decide +kernel
theorem certified5477 : Certified (graph core5477) (root 6) 0 4 :=
  of_native_maps core5477 DegreeOneSmallSpectrum1481.graph DegreeOneSmallSpectrum947.graph
    sourceMap5477 fusedMap5477 sourceMap5477_checked fusedMap5477_checked
    DegreeTwoThreeFiniteComparisons.comparison5477
#print axioms sourceMap5477_checked
#print axioms fusedMap5477_checked
#print axioms certified5477
def sourceMap5477swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap5477swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap5477swap_checked : acceptsGraphIso
    (source (graph core5477) (root 6) 4 0) DegreeOneSmallSpectrum1481.graph sourceMap5477swap=true := by decide +kernel
theorem fusedMap5477swap_checked : acceptsGraphIso
    (fused (graph core5477) (root 6) 4 0) DegreeOneSmallSpectrum947.graph fusedMap5477swap=true := by decide +kernel
theorem certified5477swap : Certified (graph core5477) (root 6) 4 0 :=
  of_native_maps core5477 DegreeOneSmallSpectrum1481.graph DegreeOneSmallSpectrum947.graph
    sourceMap5477swap fusedMap5477swap sourceMap5477swap_checked fusedMap5477swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5477
#print axioms sourceMap5477swap_checked
#print axioms fusedMap5477swap_checked
#print axioms certified5477swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
