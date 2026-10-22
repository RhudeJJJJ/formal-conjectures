/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2108 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap2108 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2108 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2108_checked : acceptsGraphIso
    (source (graph core2108) (root 7) 0 4) DegreeTwoThreeSpectrum2046.graph sourceMap2108=true := by decide +kernel
theorem fusedMap2108_checked : acceptsGraphIso
    (fused (graph core2108) (root 7) 0 4) DegreeTwoThreeSpectrum1776.graph fusedMap2108=true := by decide +kernel
theorem certified2108 : Certified (graph core2108) (root 7) 0 4 :=
  of_native_maps core2108 DegreeTwoThreeSpectrum2046.graph DegreeTwoThreeSpectrum1776.graph
    sourceMap2108 fusedMap2108 sourceMap2108_checked fusedMap2108_checked
    DegreeTwoThreeFiniteComparisons.comparison2108
#print axioms sourceMap2108_checked
#print axioms fusedMap2108_checked
#print axioms certified2108
def sourceMap2108swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2108swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2108swap_checked : acceptsGraphIso
    (source (graph core2108) (root 7) 4 0) DegreeTwoThreeSpectrum2046.graph sourceMap2108swap=true := by decide +kernel
theorem fusedMap2108swap_checked : acceptsGraphIso
    (fused (graph core2108) (root 7) 4 0) DegreeTwoThreeSpectrum1776.graph fusedMap2108swap=true := by decide +kernel
theorem certified2108swap : Certified (graph core2108) (root 7) 4 0 :=
  of_native_maps core2108 DegreeTwoThreeSpectrum2046.graph DegreeTwoThreeSpectrum1776.graph
    sourceMap2108swap fusedMap2108swap sourceMap2108swap_checked fusedMap2108swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2108
#print axioms sourceMap2108swap_checked
#print axioms fusedMap2108swap_checked
#print axioms certified2108swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
