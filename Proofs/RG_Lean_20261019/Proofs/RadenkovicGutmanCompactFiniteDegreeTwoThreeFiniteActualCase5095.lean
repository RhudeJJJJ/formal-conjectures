/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5095 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap5095 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5095 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5095_checked : acceptsGraphIso
    (source (graph core5095) (root 7) 2 4) DegreeTwoThreeSpectrum4522.graph sourceMap5095=true := by decide +kernel
theorem fusedMap5095_checked : acceptsGraphIso
    (fused (graph core5095) (root 7) 2 4) DegreeTwoThreeSpectrum4040.graph fusedMap5095=true := by decide +kernel
theorem certified5095 : Certified (graph core5095) (root 7) 2 4 :=
  of_native_maps core5095 DegreeTwoThreeSpectrum4522.graph DegreeTwoThreeSpectrum4040.graph
    sourceMap5095 fusedMap5095 sourceMap5095_checked fusedMap5095_checked
    DegreeTwoThreeFiniteComparisons.comparison5095
#print axioms sourceMap5095_checked
#print axioms fusedMap5095_checked
#print axioms certified5095
def sourceMap5095swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,15,6,7,8] (sourceLabel 7 4 2 v)
def fusedMap5095swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5095swap_checked : acceptsGraphIso
    (source (graph core5095) (root 7) 4 2) DegreeTwoThreeSpectrum4522.graph sourceMap5095swap=true := by decide +kernel
theorem fusedMap5095swap_checked : acceptsGraphIso
    (fused (graph core5095) (root 7) 4 2) DegreeTwoThreeSpectrum4040.graph fusedMap5095swap=true := by decide +kernel
theorem certified5095swap : Certified (graph core5095) (root 7) 4 2 :=
  of_native_maps core5095 DegreeTwoThreeSpectrum4522.graph DegreeTwoThreeSpectrum4040.graph
    sourceMap5095swap fusedMap5095swap sourceMap5095swap_checked fusedMap5095swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5095
#print axioms sourceMap5095swap_checked
#print axioms fusedMap5095swap_checked
#print axioms certified5095swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
