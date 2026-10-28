/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5162 : Family 8 := level8.get ⟨146,by decide⟩
def sourceMap5162 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5162 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5162_checked : acceptsGraphIso
    (source (graph core5162) (root 8) 2 4) DegreeTwoThreeSpectrum6645.graph sourceMap5162=true := by decide +kernel
theorem fusedMap5162_checked : acceptsGraphIso
    (fused (graph core5162) (root 8) 2 4) DegreeTwoThreeSpectrum5511.graph fusedMap5162=true := by decide +kernel
theorem certified5162 : Certified (graph core5162) (root 8) 2 4 :=
  of_native_maps core5162 DegreeTwoThreeSpectrum6645.graph DegreeTwoThreeSpectrum5511.graph
    sourceMap5162 fusedMap5162 sourceMap5162_checked fusedMap5162_checked
    DegreeTwoThreeFiniteComparisons.comparison5162
#print axioms sourceMap5162_checked
#print axioms fusedMap5162_checked
#print axioms certified5162
def sourceMap5162swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5162swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5162swap_checked : acceptsGraphIso
    (source (graph core5162) (root 8) 4 2) DegreeTwoThreeSpectrum6645.graph sourceMap5162swap=true := by decide +kernel
theorem fusedMap5162swap_checked : acceptsGraphIso
    (fused (graph core5162) (root 8) 4 2) DegreeTwoThreeSpectrum5511.graph fusedMap5162swap=true := by decide +kernel
theorem certified5162swap : Certified (graph core5162) (root 8) 4 2 :=
  of_native_maps core5162 DegreeTwoThreeSpectrum6645.graph DegreeTwoThreeSpectrum5511.graph
    sourceMap5162swap fusedMap5162swap sourceMap5162swap_checked fusedMap5162swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5162
#print axioms sourceMap5162swap_checked
#print axioms fusedMap5162swap_checked
#print axioms certified5162swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
