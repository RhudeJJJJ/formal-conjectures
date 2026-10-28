/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons110
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5507 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5507 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,5,6,7,2,3,4,0,8,9,10,11,12] (sourceLabel 3 2 5 v)
def fusedMap5507 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12] (fusedLabel 3 2 5 v)
theorem sourceMap5507_checked : acceptsGraphIso
    (source (graph core5507) (root 3) 2 5) DegreeOneSmallSpectrum952.graph sourceMap5507=true := by decide +kernel
theorem fusedMap5507_checked : acceptsGraphIso
    (fused (graph core5507) (root 3) 2 5) DegreeOneSmallSpectrum870.graph fusedMap5507=true := by decide +kernel
theorem certified5507 : Certified (graph core5507) (root 3) 2 5 :=
  of_native_maps core5507 DegreeOneSmallSpectrum952.graph DegreeOneSmallSpectrum870.graph
    sourceMap5507 fusedMap5507 sourceMap5507_checked fusedMap5507_checked
    DegreeTwoThreeFiniteComparisons.comparison5507
#print axioms sourceMap5507_checked
#print axioms fusedMap5507_checked
#print axioms certified5507
def sourceMap5507swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,5,6,7,0,8,9,10,11,12,2,3,4] (sourceLabel 3 5 2 v)
def fusedMap5507swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12] (fusedLabel 3 5 2 v)
theorem sourceMap5507swap_checked : acceptsGraphIso
    (source (graph core5507) (root 3) 5 2) DegreeOneSmallSpectrum952.graph sourceMap5507swap=true := by decide +kernel
theorem fusedMap5507swap_checked : acceptsGraphIso
    (fused (graph core5507) (root 3) 5 2) DegreeOneSmallSpectrum870.graph fusedMap5507swap=true := by decide +kernel
theorem certified5507swap : Certified (graph core5507) (root 3) 5 2 :=
  of_native_maps core5507 DegreeOneSmallSpectrum952.graph DegreeOneSmallSpectrum870.graph
    sourceMap5507swap fusedMap5507swap sourceMap5507swap_checked fusedMap5507swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5507
#print axioms sourceMap5507swap_checked
#print axioms fusedMap5507swap_checked
#print axioms certified5507swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
