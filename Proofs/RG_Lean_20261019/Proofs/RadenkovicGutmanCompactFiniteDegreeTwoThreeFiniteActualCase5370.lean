/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5370 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5370 : (Vertices 2 ⊕ Fin 4 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,7,8,3,4,5,6,1,0,9,10,11,12,13,14,15] (sourceLabel 2 3 8 v)
def fusedMap5370 : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 3 8 v)
theorem sourceMap5370_checked : acceptsGraphIso
    (source (graph core5370) (root 2) 3 8) DegreeTwoThreeSpectrum3878.graph sourceMap5370=true := by decide +kernel
theorem fusedMap5370_checked : acceptsGraphIso
    (fused (graph core5370) (root 2) 3 8) DegreeTwoThreeSpectrum3861.graph fusedMap5370=true := by decide +kernel
theorem certified5370 : Certified (graph core5370) (root 2) 3 8 :=
  of_native_maps core5370 DegreeTwoThreeSpectrum3878.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap5370 fusedMap5370 sourceMap5370_checked fusedMap5370_checked
    DegreeTwoThreeFiniteComparisons.comparison5370
#print axioms sourceMap5370_checked
#print axioms fusedMap5370_checked
#print axioms certified5370
def sourceMap5370swap : (Vertices 2 ⊕ Fin 9 ⊕ Fin 4) → Fin 16 :=
  fun v => ![2,7,8,1,0,9,10,11,12,13,14,15,3,4,5,6] (sourceLabel 2 8 3 v)
def fusedMap5370swap : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 8 3 v)
theorem sourceMap5370swap_checked : acceptsGraphIso
    (source (graph core5370) (root 2) 8 3) DegreeTwoThreeSpectrum3878.graph sourceMap5370swap=true := by decide +kernel
theorem fusedMap5370swap_checked : acceptsGraphIso
    (fused (graph core5370) (root 2) 8 3) DegreeTwoThreeSpectrum3861.graph fusedMap5370swap=true := by decide +kernel
theorem certified5370swap : Certified (graph core5370) (root 2) 8 3 :=
  of_native_maps core5370 DegreeTwoThreeSpectrum3878.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap5370swap fusedMap5370swap sourceMap5370swap_checked fusedMap5370swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5370
#print axioms sourceMap5370swap_checked
#print axioms fusedMap5370swap_checked
#print axioms certified5370swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
