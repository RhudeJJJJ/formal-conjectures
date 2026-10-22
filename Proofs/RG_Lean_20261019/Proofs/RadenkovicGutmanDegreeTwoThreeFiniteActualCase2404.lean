/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2404 : Family 9 := level9.get ⟨555,by decide⟩
def sourceMap2404 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2404 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2404_checked : acceptsGraphIso
    (source (graph core2404) (root 9) 0 4) DegreeTwoThreeSpectrum4684.graph sourceMap2404=true := by decide +kernel
theorem fusedMap2404_checked : acceptsGraphIso
    (fused (graph core2404) (root 9) 0 4) DegreeTwoThreeSpectrum4188.graph fusedMap2404=true := by decide +kernel
theorem certified2404 : Certified (graph core2404) (root 9) 0 4 :=
  of_native_maps core2404 DegreeTwoThreeSpectrum4684.graph DegreeTwoThreeSpectrum4188.graph
    sourceMap2404 fusedMap2404 sourceMap2404_checked fusedMap2404_checked
    DegreeTwoThreeFiniteComparisons.comparison2404
#print axioms sourceMap2404_checked
#print axioms fusedMap2404_checked
#print axioms certified2404
def sourceMap2404swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2404swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2404swap_checked : acceptsGraphIso
    (source (graph core2404) (root 9) 4 0) DegreeTwoThreeSpectrum4684.graph sourceMap2404swap=true := by decide +kernel
theorem fusedMap2404swap_checked : acceptsGraphIso
    (fused (graph core2404) (root 9) 4 0) DegreeTwoThreeSpectrum4188.graph fusedMap2404swap=true := by decide +kernel
theorem certified2404swap : Certified (graph core2404) (root 9) 4 0 :=
  of_native_maps core2404 DegreeTwoThreeSpectrum4684.graph DegreeTwoThreeSpectrum4188.graph
    sourceMap2404swap fusedMap2404swap sourceMap2404swap_checked fusedMap2404swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2404
#print axioms sourceMap2404swap_checked
#print axioms fusedMap2404swap_checked
#print axioms certified2404swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
