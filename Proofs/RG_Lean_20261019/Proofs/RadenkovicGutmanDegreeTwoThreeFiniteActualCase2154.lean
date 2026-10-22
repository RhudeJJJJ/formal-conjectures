/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2154 : Family 8 := level8.get ⟨125,by decide⟩
def sourceMap2154 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2154 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2154_checked : acceptsGraphIso
    (source (graph core2154) (root 8) 0 4) DegreeTwoThreeSpectrum2580.graph sourceMap2154=true := by decide +kernel
theorem fusedMap2154_checked : acceptsGraphIso
    (fused (graph core2154) (root 8) 0 4) DegreeTwoThreeSpectrum2582.graph fusedMap2154=true := by decide +kernel
theorem certified2154 : Certified (graph core2154) (root 8) 0 4 :=
  of_native_maps core2154 DegreeTwoThreeSpectrum2580.graph DegreeTwoThreeSpectrum2582.graph
    sourceMap2154 fusedMap2154 sourceMap2154_checked fusedMap2154_checked
    DegreeTwoThreeFiniteComparisons.comparison2154
#print axioms sourceMap2154_checked
#print axioms fusedMap2154_checked
#print axioms certified2154
def sourceMap2154swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2154swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2154swap_checked : acceptsGraphIso
    (source (graph core2154) (root 8) 4 0) DegreeTwoThreeSpectrum2580.graph sourceMap2154swap=true := by decide +kernel
theorem fusedMap2154swap_checked : acceptsGraphIso
    (fused (graph core2154) (root 8) 4 0) DegreeTwoThreeSpectrum2582.graph fusedMap2154swap=true := by decide +kernel
theorem certified2154swap : Certified (graph core2154) (root 8) 4 0 :=
  of_native_maps core2154 DegreeTwoThreeSpectrum2580.graph DegreeTwoThreeSpectrum2582.graph
    sourceMap2154swap fusedMap2154swap sourceMap2154swap_checked fusedMap2154swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2154
#print axioms sourceMap2154swap_checked
#print axioms fusedMap2154swap_checked
#print axioms certified2154swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
