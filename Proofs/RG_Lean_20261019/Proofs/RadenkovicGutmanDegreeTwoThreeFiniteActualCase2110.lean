/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2110 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap2110 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2110 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2110_checked : acceptsGraphIso
    (source (graph core2110) (root 7) 0 4) DegreeTwoThreeSpectrum2098.graph sourceMap2110=true := by decide +kernel
theorem fusedMap2110_checked : acceptsGraphIso
    (fused (graph core2110) (root 7) 0 4) DegreeTwoThreeSpectrum1808.graph fusedMap2110=true := by decide +kernel
theorem certified2110 : Certified (graph core2110) (root 7) 0 4 :=
  of_native_maps core2110 DegreeTwoThreeSpectrum2098.graph DegreeTwoThreeSpectrum1808.graph
    sourceMap2110 fusedMap2110 sourceMap2110_checked fusedMap2110_checked
    DegreeTwoThreeFiniteComparisons.comparison2110
#print axioms sourceMap2110_checked
#print axioms fusedMap2110_checked
#print axioms certified2110
def sourceMap2110swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2110swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2110swap_checked : acceptsGraphIso
    (source (graph core2110) (root 7) 4 0) DegreeTwoThreeSpectrum2098.graph sourceMap2110swap=true := by decide +kernel
theorem fusedMap2110swap_checked : acceptsGraphIso
    (fused (graph core2110) (root 7) 4 0) DegreeTwoThreeSpectrum1808.graph fusedMap2110swap=true := by decide +kernel
theorem certified2110swap : Certified (graph core2110) (root 7) 4 0 :=
  of_native_maps core2110 DegreeTwoThreeSpectrum2098.graph DegreeTwoThreeSpectrum1808.graph
    sourceMap2110swap fusedMap2110swap sourceMap2110swap_checked fusedMap2110swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2110
#print axioms sourceMap2110swap_checked
#print axioms fusedMap2110swap_checked
#print axioms certified2110swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
