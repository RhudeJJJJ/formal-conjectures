/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5415 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5415 : (Vertices 3 ⊕ Fin 5 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,7,8,9,2,3,4,5,6,0,10,11,12,13,14,15,16] (sourceLabel 3 4 7 v)
def fusedMap5415 : (Vertices 3 ⊕ Fin 13) → Fin 17 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 3 4 7 v)
theorem sourceMap5415_checked : acceptsGraphIso
    (source (graph core5415) (root 3) 4 7) DegreeTwoThreeSpectrum5108.graph sourceMap5415=true := by decide +kernel
theorem fusedMap5415_checked : acceptsGraphIso
    (fused (graph core5415) (root 3) 4 7) DegreeTwoThreeSpectrum4960.graph fusedMap5415=true := by decide +kernel
theorem certified5415 : Certified (graph core5415) (root 3) 4 7 :=
  of_native_maps core5415 DegreeTwoThreeSpectrum5108.graph DegreeTwoThreeSpectrum4960.graph
    sourceMap5415 fusedMap5415 sourceMap5415_checked fusedMap5415_checked
    DegreeTwoThreeFiniteComparisons.comparison5415
#print axioms sourceMap5415_checked
#print axioms fusedMap5415_checked
#print axioms certified5415
def sourceMap5415swap : (Vertices 3 ⊕ Fin 8 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,7,8,9,0,10,11,12,13,14,15,16,2,3,4,5,6] (sourceLabel 3 7 4 v)
def fusedMap5415swap : (Vertices 3 ⊕ Fin 13) → Fin 17 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 3 7 4 v)
theorem sourceMap5415swap_checked : acceptsGraphIso
    (source (graph core5415) (root 3) 7 4) DegreeTwoThreeSpectrum5108.graph sourceMap5415swap=true := by decide +kernel
theorem fusedMap5415swap_checked : acceptsGraphIso
    (fused (graph core5415) (root 3) 7 4) DegreeTwoThreeSpectrum4960.graph fusedMap5415swap=true := by decide +kernel
theorem certified5415swap : Certified (graph core5415) (root 3) 7 4 :=
  of_native_maps core5415 DegreeTwoThreeSpectrum5108.graph DegreeTwoThreeSpectrum4960.graph
    sourceMap5415swap fusedMap5415swap sourceMap5415swap_checked fusedMap5415swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5415
#print axioms sourceMap5415swap_checked
#print axioms fusedMap5415swap_checked
#print axioms certified5415swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
