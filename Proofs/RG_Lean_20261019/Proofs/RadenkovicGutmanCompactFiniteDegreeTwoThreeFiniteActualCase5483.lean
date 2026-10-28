/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5483 : Family 5 := level5.get ⟨12,by decide⟩
def sourceMap5483 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap5483 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap5483_checked : acceptsGraphIso
    (source (graph core5483) (root 5) 0 5) DegreeOneSmallSpectrum952.graph sourceMap5483=true := by decide +kernel
theorem fusedMap5483_checked : acceptsGraphIso
    (fused (graph core5483) (root 5) 0 5) DegreeOneSmallSpectrum956.graph fusedMap5483=true := by decide +kernel
theorem certified5483 : Certified (graph core5483) (root 5) 0 5 :=
  of_native_maps core5483 DegreeOneSmallSpectrum952.graph DegreeOneSmallSpectrum956.graph
    sourceMap5483 fusedMap5483 sourceMap5483_checked fusedMap5483_checked
    DegreeTwoThreeFiniteComparisons.comparison5483
#print axioms sourceMap5483_checked
#print axioms fusedMap5483_checked
#print axioms certified5483
def sourceMap5483swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap5483swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap5483swap_checked : acceptsGraphIso
    (source (graph core5483) (root 5) 5 0) DegreeOneSmallSpectrum952.graph sourceMap5483swap=true := by decide +kernel
theorem fusedMap5483swap_checked : acceptsGraphIso
    (fused (graph core5483) (root 5) 5 0) DegreeOneSmallSpectrum956.graph fusedMap5483swap=true := by decide +kernel
theorem certified5483swap : Certified (graph core5483) (root 5) 5 0 :=
  of_native_maps core5483 DegreeOneSmallSpectrum952.graph DegreeOneSmallSpectrum956.graph
    sourceMap5483swap fusedMap5483swap sourceMap5483swap_checked fusedMap5483swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5483
#print axioms sourceMap5483swap_checked
#print axioms fusedMap5483swap_checked
#print axioms certified5483swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
