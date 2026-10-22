/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3154 : Family 8 := level8.get ⟨64,by decide⟩
def sourceMap3154 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3154 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3154_checked : acceptsGraphIso
    (source (graph core3154) (root 8) 0 5) DegreeTwoThreeSpectrum4032.graph sourceMap3154=true := by decide +kernel
theorem fusedMap3154_checked : acceptsGraphIso
    (fused (graph core3154) (root 8) 0 5) DegreeTwoThreeSpectrum4033.graph fusedMap3154=true := by decide +kernel
theorem certified3154 : Certified (graph core3154) (root 8) 0 5 :=
  of_native_maps core3154 DegreeTwoThreeSpectrum4032.graph DegreeTwoThreeSpectrum4033.graph
    sourceMap3154 fusedMap3154 sourceMap3154_checked fusedMap3154_checked
    DegreeTwoThreeFiniteComparisons.comparison3154
#print axioms sourceMap3154_checked
#print axioms fusedMap3154_checked
#print axioms certified3154
def sourceMap3154swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3154swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3154swap_checked : acceptsGraphIso
    (source (graph core3154) (root 8) 5 0) DegreeTwoThreeSpectrum4032.graph sourceMap3154swap=true := by decide +kernel
theorem fusedMap3154swap_checked : acceptsGraphIso
    (fused (graph core3154) (root 8) 5 0) DegreeTwoThreeSpectrum4033.graph fusedMap3154swap=true := by decide +kernel
theorem certified3154swap : Certified (graph core3154) (root 8) 5 0 :=
  of_native_maps core3154 DegreeTwoThreeSpectrum4032.graph DegreeTwoThreeSpectrum4033.graph
    sourceMap3154swap fusedMap3154swap sourceMap3154swap_checked fusedMap3154swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3154
#print axioms sourceMap3154swap_checked
#print axioms fusedMap3154swap_checked
#print axioms certified3154swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
