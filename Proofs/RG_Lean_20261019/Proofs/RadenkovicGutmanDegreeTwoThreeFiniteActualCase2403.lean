/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2403 : Family 9 := level9.get ⟨554,by decide⟩
def sourceMap2403 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2403 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2403_checked : acceptsGraphIso
    (source (graph core2403) (root 9) 0 4) DegreeTwoThreeSpectrum4683.graph sourceMap2403=true := by decide +kernel
theorem fusedMap2403_checked : acceptsGraphIso
    (fused (graph core2403) (root 9) 0 4) DegreeTwoThreeSpectrum4186.graph fusedMap2403=true := by decide +kernel
theorem certified2403 : Certified (graph core2403) (root 9) 0 4 :=
  of_native_maps core2403 DegreeTwoThreeSpectrum4683.graph DegreeTwoThreeSpectrum4186.graph
    sourceMap2403 fusedMap2403 sourceMap2403_checked fusedMap2403_checked
    DegreeTwoThreeFiniteComparisons.comparison2403
#print axioms sourceMap2403_checked
#print axioms fusedMap2403_checked
#print axioms certified2403
def sourceMap2403swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2403swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2403swap_checked : acceptsGraphIso
    (source (graph core2403) (root 9) 4 0) DegreeTwoThreeSpectrum4683.graph sourceMap2403swap=true := by decide +kernel
theorem fusedMap2403swap_checked : acceptsGraphIso
    (fused (graph core2403) (root 9) 4 0) DegreeTwoThreeSpectrum4186.graph fusedMap2403swap=true := by decide +kernel
theorem certified2403swap : Certified (graph core2403) (root 9) 4 0 :=
  of_native_maps core2403 DegreeTwoThreeSpectrum4683.graph DegreeTwoThreeSpectrum4186.graph
    sourceMap2403swap fusedMap2403swap sourceMap2403swap_checked fusedMap2403swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2403
#print axioms sourceMap2403swap_checked
#print axioms fusedMap2403swap_checked
#print axioms certified2403swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
