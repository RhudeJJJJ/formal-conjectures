/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5277 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap5277 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,2,3,4,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5277 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5277_checked : acceptsGraphIso
    (source (graph core5277) (root 7) 2 5) DegreeTwoThreeSpectrum6868.graph sourceMap5277=true := by decide +kernel
theorem fusedMap5277_checked : acceptsGraphIso
    (fused (graph core5277) (root 7) 2 5) DegreeTwoThreeSpectrum5139.graph fusedMap5277=true := by decide +kernel
theorem certified5277 : Certified (graph core5277) (root 7) 2 5 :=
  of_native_maps core5277 DegreeTwoThreeSpectrum6868.graph DegreeTwoThreeSpectrum5139.graph
    sourceMap5277 fusedMap5277 sourceMap5277_checked fusedMap5277_checked
    DegreeTwoThreeFiniteComparisons.comparison5277
#print axioms sourceMap5277_checked
#print axioms fusedMap5277_checked
#print axioms certified5277
def sourceMap5277swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,0,12,13,14,15,16,2,3,4] (sourceLabel 7 5 2 v)
def fusedMap5277swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5277swap_checked : acceptsGraphIso
    (source (graph core5277) (root 7) 5 2) DegreeTwoThreeSpectrum6868.graph sourceMap5277swap=true := by decide +kernel
theorem fusedMap5277swap_checked : acceptsGraphIso
    (fused (graph core5277) (root 7) 5 2) DegreeTwoThreeSpectrum5139.graph fusedMap5277swap=true := by decide +kernel
theorem certified5277swap : Certified (graph core5277) (root 7) 5 2 :=
  of_native_maps core5277 DegreeTwoThreeSpectrum6868.graph DegreeTwoThreeSpectrum5139.graph
    sourceMap5277swap fusedMap5277swap sourceMap5277swap_checked fusedMap5277swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5277
#print axioms sourceMap5277swap_checked
#print axioms fusedMap5277swap_checked
#print axioms certified5277swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
