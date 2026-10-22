/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2350 : Family 9 := level9.get ⟨424,by decide⟩
def sourceMap2350 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2350 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2350_checked : acceptsGraphIso
    (source (graph core2350) (root 9) 0 4) DegreeTwoThreeSpectrum4410.graph sourceMap2350=true := by decide +kernel
theorem fusedMap2350_checked : acceptsGraphIso
    (fused (graph core2350) (root 9) 0 4) DegreeTwoThreeSpectrum4411.graph fusedMap2350=true := by decide +kernel
theorem certified2350 : Certified (graph core2350) (root 9) 0 4 :=
  of_native_maps core2350 DegreeTwoThreeSpectrum4410.graph DegreeTwoThreeSpectrum4411.graph
    sourceMap2350 fusedMap2350 sourceMap2350_checked fusedMap2350_checked
    DegreeTwoThreeFiniteComparisons.comparison2350
#print axioms sourceMap2350_checked
#print axioms fusedMap2350_checked
#print axioms certified2350
def sourceMap2350swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2350swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2350swap_checked : acceptsGraphIso
    (source (graph core2350) (root 9) 4 0) DegreeTwoThreeSpectrum4410.graph sourceMap2350swap=true := by decide +kernel
theorem fusedMap2350swap_checked : acceptsGraphIso
    (fused (graph core2350) (root 9) 4 0) DegreeTwoThreeSpectrum4411.graph fusedMap2350swap=true := by decide +kernel
theorem certified2350swap : Certified (graph core2350) (root 9) 4 0 :=
  of_native_maps core2350 DegreeTwoThreeSpectrum4410.graph DegreeTwoThreeSpectrum4411.graph
    sourceMap2350swap fusedMap2350swap sourceMap2350swap_checked fusedMap2350swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2350
#print axioms sourceMap2350swap_checked
#print axioms fusedMap2350swap_checked
#print axioms certified2350swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
