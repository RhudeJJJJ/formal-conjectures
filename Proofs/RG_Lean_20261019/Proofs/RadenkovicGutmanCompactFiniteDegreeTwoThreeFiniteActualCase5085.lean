/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5085 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap5085 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,12,13,14,7,8,9,10,11] (sourceLabel 7 2 4 v)
def fusedMap5085 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5085_checked : acceptsGraphIso
    (source (graph core5085) (root 7) 2 4) DegreeTwoThreeSpectrum4623.graph sourceMap5085=true := by decide +kernel
theorem fusedMap5085_checked : acceptsGraphIso
    (fused (graph core5085) (root 7) 2 4) DegreeTwoThreeSpectrum3873.graph fusedMap5085=true := by decide +kernel
theorem certified5085 : Certified (graph core5085) (root 7) 2 4 :=
  of_native_maps core5085 DegreeTwoThreeSpectrum4623.graph DegreeTwoThreeSpectrum3873.graph
    sourceMap5085 fusedMap5085 sourceMap5085_checked fusedMap5085_checked
    DegreeTwoThreeFiniteComparisons.comparison5085
#print axioms sourceMap5085_checked
#print axioms fusedMap5085_checked
#print axioms certified5085
def sourceMap5085swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,7,8,9,10,11,12,13,14] (sourceLabel 7 4 2 v)
def fusedMap5085swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5085swap_checked : acceptsGraphIso
    (source (graph core5085) (root 7) 4 2) DegreeTwoThreeSpectrum4623.graph sourceMap5085swap=true := by decide +kernel
theorem fusedMap5085swap_checked : acceptsGraphIso
    (fused (graph core5085) (root 7) 4 2) DegreeTwoThreeSpectrum3873.graph fusedMap5085swap=true := by decide +kernel
theorem certified5085swap : Certified (graph core5085) (root 7) 4 2 :=
  of_native_maps core5085 DegreeTwoThreeSpectrum4623.graph DegreeTwoThreeSpectrum3873.graph
    sourceMap5085swap fusedMap5085swap sourceMap5085swap_checked fusedMap5085swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5085
#print axioms sourceMap5085swap_checked
#print axioms fusedMap5085swap_checked
#print axioms certified5085swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
