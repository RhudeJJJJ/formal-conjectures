/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5488 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5488 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (sourceLabel 3 0 7 v)
def fusedMap5488 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12] (fusedLabel 3 0 7 v)
theorem sourceMap5488_checked : acceptsGraphIso
    (source (graph core5488) (root 3) 0 7) DegreeOneSmallSpectrum862.graph sourceMap5488=true := by decide +kernel
theorem fusedMap5488_checked : acceptsGraphIso
    (fused (graph core5488) (root 3) 0 7) DegreeOneSmallSpectrum870.graph fusedMap5488=true := by decide +kernel
theorem certified5488 : Certified (graph core5488) (root 3) 0 7 :=
  of_native_maps core5488 DegreeOneSmallSpectrum862.graph DegreeOneSmallSpectrum870.graph
    sourceMap5488 fusedMap5488 sourceMap5488_checked fusedMap5488_checked
    DegreeTwoThreeFiniteComparisons.comparison5488
#print axioms sourceMap5488_checked
#print axioms fusedMap5488_checked
#print axioms certified5488
def sourceMap5488swap : (Vertices 3 ⊕ Fin 8 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,8,9,10,11,12,7] (sourceLabel 3 7 0 v)
def fusedMap5488swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12] (fusedLabel 3 7 0 v)
theorem sourceMap5488swap_checked : acceptsGraphIso
    (source (graph core5488) (root 3) 7 0) DegreeOneSmallSpectrum862.graph sourceMap5488swap=true := by decide +kernel
theorem fusedMap5488swap_checked : acceptsGraphIso
    (fused (graph core5488) (root 3) 7 0) DegreeOneSmallSpectrum870.graph fusedMap5488swap=true := by decide +kernel
theorem certified5488swap : Certified (graph core5488) (root 3) 7 0 :=
  of_native_maps core5488 DegreeOneSmallSpectrum862.graph DegreeOneSmallSpectrum870.graph
    sourceMap5488swap fusedMap5488swap sourceMap5488swap_checked fusedMap5488swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5488
#print axioms sourceMap5488swap_checked
#print axioms fusedMap5488swap_checked
#print axioms certified5488swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
