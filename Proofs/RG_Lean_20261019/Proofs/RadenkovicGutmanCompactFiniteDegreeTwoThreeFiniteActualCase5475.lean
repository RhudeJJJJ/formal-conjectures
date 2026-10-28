/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5475 : Family 6 := level6.get ⟨26,by decide⟩
def sourceMap5475 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap5475 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap5475_checked : acceptsGraphIso
    (source (graph core5475) (root 6) 0 4) DegreeOneSmallSpectrum1216.graph sourceMap5475=true := by decide +kernel
theorem fusedMap5475_checked : acceptsGraphIso
    (fused (graph core5475) (root 6) 0 4) DegreeOneSmallSpectrum881.graph fusedMap5475=true := by decide +kernel
theorem certified5475 : Certified (graph core5475) (root 6) 0 4 :=
  of_native_maps core5475 DegreeOneSmallSpectrum1216.graph DegreeOneSmallSpectrum881.graph
    sourceMap5475 fusedMap5475 sourceMap5475_checked fusedMap5475_checked
    DegreeTwoThreeFiniteComparisons.comparison5475
#print axioms sourceMap5475_checked
#print axioms fusedMap5475_checked
#print axioms certified5475
def sourceMap5475swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap5475swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap5475swap_checked : acceptsGraphIso
    (source (graph core5475) (root 6) 4 0) DegreeOneSmallSpectrum1216.graph sourceMap5475swap=true := by decide +kernel
theorem fusedMap5475swap_checked : acceptsGraphIso
    (fused (graph core5475) (root 6) 4 0) DegreeOneSmallSpectrum881.graph fusedMap5475swap=true := by decide +kernel
theorem certified5475swap : Certified (graph core5475) (root 6) 4 0 :=
  of_native_maps core5475 DegreeOneSmallSpectrum1216.graph DegreeOneSmallSpectrum881.graph
    sourceMap5475swap fusedMap5475swap sourceMap5475swap_checked fusedMap5475swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5475
#print axioms sourceMap5475swap_checked
#print axioms fusedMap5475swap_checked
#print axioms certified5475swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
