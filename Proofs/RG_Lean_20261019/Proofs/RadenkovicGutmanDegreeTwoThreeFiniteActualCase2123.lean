/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2123 : Family 8 := level8.get ⟨28,by decide⟩
def sourceMap2123 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2123 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 0 4 v)
theorem sourceMap2123_checked : acceptsGraphIso
    (source (graph core2123) (root 8) 0 4) DegreeTwoThreeSpectrum2425.graph sourceMap2123=true := by decide +kernel
theorem fusedMap2123_checked : acceptsGraphIso
    (fused (graph core2123) (root 8) 0 4) DegreeTwoThreeSpectrum2427.graph fusedMap2123=true := by decide +kernel
theorem certified2123 : Certified (graph core2123) (root 8) 0 4 :=
  of_native_maps core2123 DegreeTwoThreeSpectrum2425.graph DegreeTwoThreeSpectrum2427.graph
    sourceMap2123 fusedMap2123 sourceMap2123_checked fusedMap2123_checked
    DegreeTwoThreeFiniteComparisons.comparison2123
#print axioms sourceMap2123_checked
#print axioms fusedMap2123_checked
#print axioms certified2123
def sourceMap2123swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2123swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 4 0 v)
theorem sourceMap2123swap_checked : acceptsGraphIso
    (source (graph core2123) (root 8) 4 0) DegreeTwoThreeSpectrum2425.graph sourceMap2123swap=true := by decide +kernel
theorem fusedMap2123swap_checked : acceptsGraphIso
    (fused (graph core2123) (root 8) 4 0) DegreeTwoThreeSpectrum2427.graph fusedMap2123swap=true := by decide +kernel
theorem certified2123swap : Certified (graph core2123) (root 8) 4 0 :=
  of_native_maps core2123 DegreeTwoThreeSpectrum2425.graph DegreeTwoThreeSpectrum2427.graph
    sourceMap2123swap fusedMap2123swap sourceMap2123swap_checked fusedMap2123swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2123
#print axioms sourceMap2123swap_checked
#print axioms fusedMap2123swap_checked
#print axioms certified2123swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
