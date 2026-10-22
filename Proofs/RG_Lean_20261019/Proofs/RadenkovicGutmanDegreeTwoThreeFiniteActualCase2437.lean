/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2437 : Family 9 := level9.get ⟨636,by decide⟩
def sourceMap2437 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2437 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2437_checked : acceptsGraphIso
    (source (graph core2437) (root 9) 0 4) DegreeTwoThreeSpectrum4793.graph sourceMap2437=true := by decide +kernel
theorem fusedMap2437_checked : acceptsGraphIso
    (fused (graph core2437) (root 9) 0 4) DegreeTwoThreeSpectrum4398.graph fusedMap2437=true := by decide +kernel
theorem certified2437 : Certified (graph core2437) (root 9) 0 4 :=
  of_native_maps core2437 DegreeTwoThreeSpectrum4793.graph DegreeTwoThreeSpectrum4398.graph
    sourceMap2437 fusedMap2437 sourceMap2437_checked fusedMap2437_checked
    DegreeTwoThreeFiniteComparisons.comparison2437
#print axioms sourceMap2437_checked
#print axioms fusedMap2437_checked
#print axioms certified2437
def sourceMap2437swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2437swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2437swap_checked : acceptsGraphIso
    (source (graph core2437) (root 9) 4 0) DegreeTwoThreeSpectrum4793.graph sourceMap2437swap=true := by decide +kernel
theorem fusedMap2437swap_checked : acceptsGraphIso
    (fused (graph core2437) (root 9) 4 0) DegreeTwoThreeSpectrum4398.graph fusedMap2437swap=true := by decide +kernel
theorem certified2437swap : Certified (graph core2437) (root 9) 4 0 :=
  of_native_maps core2437 DegreeTwoThreeSpectrum4793.graph DegreeTwoThreeSpectrum4398.graph
    sourceMap2437swap fusedMap2437swap sourceMap2437swap_checked fusedMap2437swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2437
#print axioms sourceMap2437swap_checked
#print axioms fusedMap2437swap_checked
#print axioms certified2437swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
