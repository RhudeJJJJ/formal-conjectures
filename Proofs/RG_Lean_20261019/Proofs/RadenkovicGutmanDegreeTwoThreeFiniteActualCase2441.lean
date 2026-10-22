/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2441 : Family 9 := level9.get ⟨644,by decide⟩
def sourceMap2441 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2441 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2441_checked : acceptsGraphIso
    (source (graph core2441) (root 9) 0 4) DegreeTwoThreeSpectrum4804.graph sourceMap2441=true := by decide +kernel
theorem fusedMap2441_checked : acceptsGraphIso
    (fused (graph core2441) (root 9) 0 4) DegreeTwoThreeSpectrum4417.graph fusedMap2441=true := by decide +kernel
theorem certified2441 : Certified (graph core2441) (root 9) 0 4 :=
  of_native_maps core2441 DegreeTwoThreeSpectrum4804.graph DegreeTwoThreeSpectrum4417.graph
    sourceMap2441 fusedMap2441 sourceMap2441_checked fusedMap2441_checked
    DegreeTwoThreeFiniteComparisons.comparison2441
#print axioms sourceMap2441_checked
#print axioms fusedMap2441_checked
#print axioms certified2441
def sourceMap2441swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2441swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2441swap_checked : acceptsGraphIso
    (source (graph core2441) (root 9) 4 0) DegreeTwoThreeSpectrum4804.graph sourceMap2441swap=true := by decide +kernel
theorem fusedMap2441swap_checked : acceptsGraphIso
    (fused (graph core2441) (root 9) 4 0) DegreeTwoThreeSpectrum4417.graph fusedMap2441swap=true := by decide +kernel
theorem certified2441swap : Certified (graph core2441) (root 9) 4 0 :=
  of_native_maps core2441 DegreeTwoThreeSpectrum4804.graph DegreeTwoThreeSpectrum4417.graph
    sourceMap2441swap fusedMap2441swap sourceMap2441swap_checked fusedMap2441swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2441
#print axioms sourceMap2441swap_checked
#print axioms fusedMap2441swap_checked
#print axioms certified2441swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
