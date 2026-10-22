/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3967 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap3967 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3967 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3967_checked : acceptsGraphIso
    (source (graph core3967) (root 7) 1 5) DegreeTwoThreeSpectrum4642.graph sourceMap3967=true := by decide +kernel
theorem fusedMap3967_checked : acceptsGraphIso
    (fused (graph core3967) (root 7) 1 5) DegreeTwoThreeSpectrum4120.graph fusedMap3967=true := by decide +kernel
theorem certified3967 : Certified (graph core3967) (root 7) 1 5 :=
  of_native_maps core3967 DegreeTwoThreeSpectrum4642.graph DegreeTwoThreeSpectrum4120.graph
    sourceMap3967 fusedMap3967 sourceMap3967_checked fusedMap3967_checked
    DegreeTwoThreeFiniteComparisons.comparison3967
#print axioms sourceMap3967_checked
#print axioms fusedMap3967_checked
#print axioms certified3967
def sourceMap3967swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3967swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3967swap_checked : acceptsGraphIso
    (source (graph core3967) (root 7) 5 1) DegreeTwoThreeSpectrum4642.graph sourceMap3967swap=true := by decide +kernel
theorem fusedMap3967swap_checked : acceptsGraphIso
    (fused (graph core3967) (root 7) 5 1) DegreeTwoThreeSpectrum4120.graph fusedMap3967swap=true := by decide +kernel
theorem certified3967swap : Certified (graph core3967) (root 7) 5 1 :=
  of_native_maps core3967 DegreeTwoThreeSpectrum4642.graph DegreeTwoThreeSpectrum4120.graph
    sourceMap3967swap fusedMap3967swap sourceMap3967swap_checked fusedMap3967swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3967
#print axioms sourceMap3967swap_checked
#print axioms fusedMap3967swap_checked
#print axioms certified3967swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
