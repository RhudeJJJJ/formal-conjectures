/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3192 : Family 8 := level8.get ⟨168,by decide⟩
def sourceMap3192 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3192 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3192_checked : acceptsGraphIso
    (source (graph core3192) (root 8) 0 5) DegreeTwoThreeSpectrum4583.graph sourceMap3192=true := by decide +kernel
theorem fusedMap3192_checked : acceptsGraphIso
    (fused (graph core3192) (root 8) 0 5) DegreeTwoThreeSpectrum4069.graph fusedMap3192=true := by decide +kernel
theorem certified3192 : Certified (graph core3192) (root 8) 0 5 :=
  of_native_maps core3192 DegreeTwoThreeSpectrum4583.graph DegreeTwoThreeSpectrum4069.graph
    sourceMap3192 fusedMap3192 sourceMap3192_checked fusedMap3192_checked
    DegreeTwoThreeFiniteComparisons.comparison3192
#print axioms sourceMap3192_checked
#print axioms fusedMap3192_checked
#print axioms certified3192
def sourceMap3192swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3192swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3192swap_checked : acceptsGraphIso
    (source (graph core3192) (root 8) 5 0) DegreeTwoThreeSpectrum4583.graph sourceMap3192swap=true := by decide +kernel
theorem fusedMap3192swap_checked : acceptsGraphIso
    (fused (graph core3192) (root 8) 5 0) DegreeTwoThreeSpectrum4069.graph fusedMap3192swap=true := by decide +kernel
theorem certified3192swap : Certified (graph core3192) (root 8) 5 0 :=
  of_native_maps core3192 DegreeTwoThreeSpectrum4583.graph DegreeTwoThreeSpectrum4069.graph
    sourceMap3192swap fusedMap3192swap sourceMap3192swap_checked fusedMap3192swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3192
#print axioms sourceMap3192swap_checked
#print axioms fusedMap3192swap_checked
#print axioms certified3192swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
