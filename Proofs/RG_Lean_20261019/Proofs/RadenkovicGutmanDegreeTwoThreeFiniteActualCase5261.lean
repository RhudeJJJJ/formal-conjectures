/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5261 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap5261 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5261 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5261_checked : acceptsGraphIso
    (source (graph core5261) (root 7) 2 5) DegreeTwoThreeSpectrum6023.graph sourceMap5261=true := by decide +kernel
theorem fusedMap5261_checked : acceptsGraphIso
    (fused (graph core5261) (root 7) 2 5) DegreeTwoThreeSpectrum5149.graph fusedMap5261=true := by decide +kernel
theorem certified5261 : Certified (graph core5261) (root 7) 2 5 :=
  of_native_maps core5261 DegreeTwoThreeSpectrum6023.graph DegreeTwoThreeSpectrum5149.graph
    sourceMap5261 fusedMap5261 sourceMap5261_checked fusedMap5261_checked
    DegreeTwoThreeFiniteComparisons.comparison5261
#print axioms sourceMap5261_checked
#print axioms fusedMap5261_checked
#print axioms certified5261
def sourceMap5261swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5261swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5261swap_checked : acceptsGraphIso
    (source (graph core5261) (root 7) 5 2) DegreeTwoThreeSpectrum6023.graph sourceMap5261swap=true := by decide +kernel
theorem fusedMap5261swap_checked : acceptsGraphIso
    (fused (graph core5261) (root 7) 5 2) DegreeTwoThreeSpectrum5149.graph fusedMap5261swap=true := by decide +kernel
theorem certified5261swap : Certified (graph core5261) (root 7) 5 2 :=
  of_native_maps core5261 DegreeTwoThreeSpectrum6023.graph DegreeTwoThreeSpectrum5149.graph
    sourceMap5261swap fusedMap5261swap sourceMap5261swap_checked fusedMap5261swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5261
#print axioms sourceMap5261swap_checked
#print axioms fusedMap5261swap_checked
#print axioms certified5261swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
