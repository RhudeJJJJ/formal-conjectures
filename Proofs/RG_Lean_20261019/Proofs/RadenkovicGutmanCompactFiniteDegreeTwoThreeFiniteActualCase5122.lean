/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5122 : Family 8 := level8.get ⟨24,by decide⟩
def sourceMap5122 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5122 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5122_checked : acceptsGraphIso
    (source (graph core5122) (root 8) 2 4) DegreeTwoThreeSpectrum5811.graph sourceMap5122=true := by decide +kernel
theorem fusedMap5122_checked : acceptsGraphIso
    (fused (graph core5122) (root 8) 2 4) DegreeTwoThreeSpectrum5075.graph fusedMap5122=true := by decide +kernel
theorem certified5122 : Certified (graph core5122) (root 8) 2 4 :=
  of_native_maps core5122 DegreeTwoThreeSpectrum5811.graph DegreeTwoThreeSpectrum5075.graph
    sourceMap5122 fusedMap5122 sourceMap5122_checked fusedMap5122_checked
    DegreeTwoThreeFiniteComparisons.comparison5122
#print axioms sourceMap5122_checked
#print axioms fusedMap5122_checked
#print axioms certified5122
def sourceMap5122swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5122swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5122swap_checked : acceptsGraphIso
    (source (graph core5122) (root 8) 4 2) DegreeTwoThreeSpectrum5811.graph sourceMap5122swap=true := by decide +kernel
theorem fusedMap5122swap_checked : acceptsGraphIso
    (fused (graph core5122) (root 8) 4 2) DegreeTwoThreeSpectrum5075.graph fusedMap5122swap=true := by decide +kernel
theorem certified5122swap : Certified (graph core5122) (root 8) 4 2 :=
  of_native_maps core5122 DegreeTwoThreeSpectrum5811.graph DegreeTwoThreeSpectrum5075.graph
    sourceMap5122swap fusedMap5122swap sourceMap5122swap_checked fusedMap5122swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5122
#print axioms sourceMap5122swap_checked
#print axioms fusedMap5122swap_checked
#print axioms certified5122swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
