/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5414 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5414 : (Vertices 2 ⊕ Fin 5 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,7,8,2,3,4,5,6,0,9,10,11,12,13,14,15] (sourceLabel 2 4 7 v)
def fusedMap5414 : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 4 7 v)
theorem sourceMap5414_checked : acceptsGraphIso
    (source (graph core5414) (root 2) 4 7) DegreeTwoThreeSpectrum3884.graph sourceMap5414=true := by decide +kernel
theorem fusedMap5414_checked : acceptsGraphIso
    (fused (graph core5414) (root 2) 4 7) DegreeTwoThreeSpectrum3861.graph fusedMap5414=true := by decide +kernel
theorem certified5414 : Certified (graph core5414) (root 2) 4 7 :=
  of_native_maps core5414 DegreeTwoThreeSpectrum3884.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap5414 fusedMap5414 sourceMap5414_checked fusedMap5414_checked
    DegreeTwoThreeFiniteComparisons.comparison5414
#print axioms sourceMap5414_checked
#print axioms fusedMap5414_checked
#print axioms certified5414
def sourceMap5414swap : (Vertices 2 ⊕ Fin 8 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,7,8,0,9,10,11,12,13,14,15,2,3,4,5,6] (sourceLabel 2 7 4 v)
def fusedMap5414swap : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 7 4 v)
theorem sourceMap5414swap_checked : acceptsGraphIso
    (source (graph core5414) (root 2) 7 4) DegreeTwoThreeSpectrum3884.graph sourceMap5414swap=true := by decide +kernel
theorem fusedMap5414swap_checked : acceptsGraphIso
    (fused (graph core5414) (root 2) 7 4) DegreeTwoThreeSpectrum3861.graph fusedMap5414swap=true := by decide +kernel
theorem certified5414swap : Certified (graph core5414) (root 2) 7 4 :=
  of_native_maps core5414 DegreeTwoThreeSpectrum3884.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap5414swap fusedMap5414swap sourceMap5414swap_checked fusedMap5414swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5414
#print axioms sourceMap5414swap_checked
#print axioms fusedMap5414swap_checked
#print axioms certified5414swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
