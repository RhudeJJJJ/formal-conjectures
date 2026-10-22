/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2197 : Family 8 := level8.get ⟨223,by decide⟩
def sourceMap2197 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2197 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2197_checked : acceptsGraphIso
    (source (graph core2197) (root 8) 0 4) DegreeTwoThreeSpectrum3284.graph sourceMap2197=true := by decide +kernel
theorem fusedMap2197_checked : acceptsGraphIso
    (fused (graph core2197) (root 8) 0 4) DegreeTwoThreeSpectrum2562.graph fusedMap2197=true := by decide +kernel
theorem certified2197 : Certified (graph core2197) (root 8) 0 4 :=
  of_native_maps core2197 DegreeTwoThreeSpectrum3284.graph DegreeTwoThreeSpectrum2562.graph
    sourceMap2197 fusedMap2197 sourceMap2197_checked fusedMap2197_checked
    DegreeTwoThreeFiniteComparisons.comparison2197
#print axioms sourceMap2197_checked
#print axioms fusedMap2197_checked
#print axioms certified2197
def sourceMap2197swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2197swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2197swap_checked : acceptsGraphIso
    (source (graph core2197) (root 8) 4 0) DegreeTwoThreeSpectrum3284.graph sourceMap2197swap=true := by decide +kernel
theorem fusedMap2197swap_checked : acceptsGraphIso
    (fused (graph core2197) (root 8) 4 0) DegreeTwoThreeSpectrum2562.graph fusedMap2197swap=true := by decide +kernel
theorem certified2197swap : Certified (graph core2197) (root 8) 4 0 :=
  of_native_maps core2197 DegreeTwoThreeSpectrum3284.graph DegreeTwoThreeSpectrum2562.graph
    sourceMap2197swap fusedMap2197swap sourceMap2197swap_checked fusedMap2197swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2197
#print axioms sourceMap2197swap_checked
#print axioms fusedMap2197swap_checked
#print axioms certified2197swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
