/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5101 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap5101 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5101 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5101_checked : acceptsGraphIso
    (source (graph core5101) (root 7) 2 4) DegreeTwoThreeSpectrum4686.graph sourceMap5101=true := by decide +kernel
theorem fusedMap5101_checked : acceptsGraphIso
    (fused (graph core5101) (root 7) 2 4) DegreeTwoThreeSpectrum3894.graph fusedMap5101=true := by decide +kernel
theorem certified5101 : Certified (graph core5101) (root 7) 2 4 :=
  of_native_maps core5101 DegreeTwoThreeSpectrum4686.graph DegreeTwoThreeSpectrum3894.graph
    sourceMap5101 fusedMap5101 sourceMap5101_checked fusedMap5101_checked
    DegreeTwoThreeFiniteComparisons.comparison5101
#print axioms sourceMap5101_checked
#print axioms fusedMap5101_checked
#print axioms certified5101
def sourceMap5101swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,8,9,10] (sourceLabel 7 4 2 v)
def fusedMap5101swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5101swap_checked : acceptsGraphIso
    (source (graph core5101) (root 7) 4 2) DegreeTwoThreeSpectrum4686.graph sourceMap5101swap=true := by decide +kernel
theorem fusedMap5101swap_checked : acceptsGraphIso
    (fused (graph core5101) (root 7) 4 2) DegreeTwoThreeSpectrum3894.graph fusedMap5101swap=true := by decide +kernel
theorem certified5101swap : Certified (graph core5101) (root 7) 4 2 :=
  of_native_maps core5101 DegreeTwoThreeSpectrum4686.graph DegreeTwoThreeSpectrum3894.graph
    sourceMap5101swap fusedMap5101swap sourceMap5101swap_checked fusedMap5101swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5101
#print axioms sourceMap5101swap_checked
#print axioms fusedMap5101swap_checked
#print axioms certified5101swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
