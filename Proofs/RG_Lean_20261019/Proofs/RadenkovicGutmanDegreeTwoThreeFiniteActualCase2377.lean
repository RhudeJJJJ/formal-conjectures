/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2377 : Family 9 := level9.get ⟨489,by decide⟩
def sourceMap2377 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2377 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2377_checked : acceptsGraphIso
    (source (graph core2377) (root 9) 0 4) DegreeTwoThreeSpectrum4558.graph sourceMap2377=true := by decide +kernel
theorem fusedMap2377_checked : acceptsGraphIso
    (fused (graph core2377) (root 9) 0 4) DegreeTwoThreeSpectrum4559.graph fusedMap2377=true := by decide +kernel
theorem certified2377 : Certified (graph core2377) (root 9) 0 4 :=
  of_native_maps core2377 DegreeTwoThreeSpectrum4558.graph DegreeTwoThreeSpectrum4559.graph
    sourceMap2377 fusedMap2377 sourceMap2377_checked fusedMap2377_checked
    DegreeTwoThreeFiniteComparisons.comparison2377
#print axioms sourceMap2377_checked
#print axioms fusedMap2377_checked
#print axioms certified2377
def sourceMap2377swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2377swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2377swap_checked : acceptsGraphIso
    (source (graph core2377) (root 9) 4 0) DegreeTwoThreeSpectrum4558.graph sourceMap2377swap=true := by decide +kernel
theorem fusedMap2377swap_checked : acceptsGraphIso
    (fused (graph core2377) (root 9) 4 0) DegreeTwoThreeSpectrum4559.graph fusedMap2377swap=true := by decide +kernel
theorem certified2377swap : Certified (graph core2377) (root 9) 4 0 :=
  of_native_maps core2377 DegreeTwoThreeSpectrum4558.graph DegreeTwoThreeSpectrum4559.graph
    sourceMap2377swap fusedMap2377swap sourceMap2377swap_checked fusedMap2377swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2377
#print axioms sourceMap2377swap_checked
#print axioms fusedMap2377swap_checked
#print axioms certified2377swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
