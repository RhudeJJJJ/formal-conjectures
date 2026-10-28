/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5168 : Family 8 := level8.get ⟨158,by decide⟩
def sourceMap5168 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5168 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5168_checked : acceptsGraphIso
    (source (graph core5168) (root 8) 2 4) DegreeTwoThreeSpectrum6763.graph sourceMap5168=true := by decide +kernel
theorem fusedMap5168_checked : acceptsGraphIso
    (fused (graph core5168) (root 8) 2 4) DegreeTwoThreeSpectrum5605.graph fusedMap5168=true := by decide +kernel
theorem certified5168 : Certified (graph core5168) (root 8) 2 4 :=
  of_native_maps core5168 DegreeTwoThreeSpectrum6763.graph DegreeTwoThreeSpectrum5605.graph
    sourceMap5168 fusedMap5168 sourceMap5168_checked fusedMap5168_checked
    DegreeTwoThreeFiniteComparisons.comparison5168
#print axioms sourceMap5168_checked
#print axioms fusedMap5168_checked
#print axioms certified5168
def sourceMap5168swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,15,16,6,7,8] (sourceLabel 8 4 2 v)
def fusedMap5168swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5168swap_checked : acceptsGraphIso
    (source (graph core5168) (root 8) 4 2) DegreeTwoThreeSpectrum6763.graph sourceMap5168swap=true := by decide +kernel
theorem fusedMap5168swap_checked : acceptsGraphIso
    (fused (graph core5168) (root 8) 4 2) DegreeTwoThreeSpectrum5605.graph fusedMap5168swap=true := by decide +kernel
theorem certified5168swap : Certified (graph core5168) (root 8) 4 2 :=
  of_native_maps core5168 DegreeTwoThreeSpectrum6763.graph DegreeTwoThreeSpectrum5605.graph
    sourceMap5168swap fusedMap5168swap sourceMap5168swap_checked fusedMap5168swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5168
#print axioms sourceMap5168swap_checked
#print axioms fusedMap5168swap_checked
#print axioms certified5168swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
