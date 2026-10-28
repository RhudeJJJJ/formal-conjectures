/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5272 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap5272 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5272 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5272_checked : acceptsGraphIso
    (source (graph core5272) (root 7) 2 5) DegreeTwoThreeSpectrum6623.graph sourceMap5272=true := by decide +kernel
theorem fusedMap5272_checked : acceptsGraphIso
    (fused (graph core5272) (root 7) 2 5) DegreeTwoThreeSpectrum5504.graph fusedMap5272=true := by decide +kernel
theorem certified5272 : Certified (graph core5272) (root 7) 2 5 :=
  of_native_maps core5272 DegreeTwoThreeSpectrum6623.graph DegreeTwoThreeSpectrum5504.graph
    sourceMap5272 fusedMap5272 sourceMap5272_checked fusedMap5272_checked
    DegreeTwoThreeFiniteComparisons.comparison5272
#print axioms sourceMap5272_checked
#print axioms fusedMap5272_checked
#print axioms certified5272
def sourceMap5272swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5272swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5272swap_checked : acceptsGraphIso
    (source (graph core5272) (root 7) 5 2) DegreeTwoThreeSpectrum6623.graph sourceMap5272swap=true := by decide +kernel
theorem fusedMap5272swap_checked : acceptsGraphIso
    (fused (graph core5272) (root 7) 5 2) DegreeTwoThreeSpectrum5504.graph fusedMap5272swap=true := by decide +kernel
theorem certified5272swap : Certified (graph core5272) (root 7) 5 2 :=
  of_native_maps core5272 DegreeTwoThreeSpectrum6623.graph DegreeTwoThreeSpectrum5504.graph
    sourceMap5272swap fusedMap5272swap sourceMap5272swap_checked fusedMap5272swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5272
#print axioms sourceMap5272swap_checked
#print axioms fusedMap5272swap_checked
#print axioms certified5272swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
