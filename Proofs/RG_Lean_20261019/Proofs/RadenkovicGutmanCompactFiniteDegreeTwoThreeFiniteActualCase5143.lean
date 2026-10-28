/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5143 : Family 8 := level8.get ⟨91,by decide⟩
def sourceMap5143 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,16,6,7,8,9,10] (sourceLabel 8 2 4 v)
def fusedMap5143 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5143_checked : acceptsGraphIso
    (source (graph core5143) (root 8) 2 4) DegreeTwoThreeSpectrum7052.graph sourceMap5143=true := by decide +kernel
theorem fusedMap5143_checked : acceptsGraphIso
    (fused (graph core5143) (root 8) 2 4) DegreeTwoThreeSpectrum5106.graph fusedMap5143=true := by decide +kernel
theorem certified5143 : Certified (graph core5143) (root 8) 2 4 :=
  of_native_maps core5143 DegreeTwoThreeSpectrum7052.graph DegreeTwoThreeSpectrum5106.graph
    sourceMap5143 fusedMap5143 sourceMap5143_checked fusedMap5143_checked
    DegreeTwoThreeFiniteComparisons.comparison5143
#print axioms sourceMap5143_checked
#print axioms fusedMap5143_checked
#print axioms certified5143
def sourceMap5143swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,6,7,8,9,10,14,15,16] (sourceLabel 8 4 2 v)
def fusedMap5143swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5143swap_checked : acceptsGraphIso
    (source (graph core5143) (root 8) 4 2) DegreeTwoThreeSpectrum7052.graph sourceMap5143swap=true := by decide +kernel
theorem fusedMap5143swap_checked : acceptsGraphIso
    (fused (graph core5143) (root 8) 4 2) DegreeTwoThreeSpectrum5106.graph fusedMap5143swap=true := by decide +kernel
theorem certified5143swap : Certified (graph core5143) (root 8) 4 2 :=
  of_native_maps core5143 DegreeTwoThreeSpectrum7052.graph DegreeTwoThreeSpectrum5106.graph
    sourceMap5143swap fusedMap5143swap sourceMap5143swap_checked fusedMap5143swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5143
#print axioms sourceMap5143swap_checked
#print axioms fusedMap5143swap_checked
#print axioms certified5143swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
