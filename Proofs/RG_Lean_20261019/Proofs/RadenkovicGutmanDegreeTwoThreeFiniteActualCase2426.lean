/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2426 : Family 9 := level9.get ⟨604,by decide⟩
def sourceMap2426 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2426 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2426_checked : acceptsGraphIso
    (source (graph core2426) (root 9) 0 4) DegreeTwoThreeSpectrum4738.graph sourceMap2426=true := by decide +kernel
theorem fusedMap2426_checked : acceptsGraphIso
    (fused (graph core2426) (root 9) 0 4) DegreeTwoThreeSpectrum4292.graph fusedMap2426=true := by decide +kernel
theorem certified2426 : Certified (graph core2426) (root 9) 0 4 :=
  of_native_maps core2426 DegreeTwoThreeSpectrum4738.graph DegreeTwoThreeSpectrum4292.graph
    sourceMap2426 fusedMap2426 sourceMap2426_checked fusedMap2426_checked
    DegreeTwoThreeFiniteComparisons.comparison2426
#print axioms sourceMap2426_checked
#print axioms fusedMap2426_checked
#print axioms certified2426
def sourceMap2426swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2426swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2426swap_checked : acceptsGraphIso
    (source (graph core2426) (root 9) 4 0) DegreeTwoThreeSpectrum4738.graph sourceMap2426swap=true := by decide +kernel
theorem fusedMap2426swap_checked : acceptsGraphIso
    (fused (graph core2426) (root 9) 4 0) DegreeTwoThreeSpectrum4292.graph fusedMap2426swap=true := by decide +kernel
theorem certified2426swap : Certified (graph core2426) (root 9) 4 0 :=
  of_native_maps core2426 DegreeTwoThreeSpectrum4738.graph DegreeTwoThreeSpectrum4292.graph
    sourceMap2426swap fusedMap2426swap sourceMap2426swap_checked fusedMap2426swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2426
#print axioms sourceMap2426swap_checked
#print axioms fusedMap2426swap_checked
#print axioms certified2426swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
