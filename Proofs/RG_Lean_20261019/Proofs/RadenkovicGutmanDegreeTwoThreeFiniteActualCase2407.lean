/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2407 : Family 9 := level9.get ⟨563,by decide⟩
def sourceMap2407 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2407 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2407_checked : acceptsGraphIso
    (source (graph core2407) (root 9) 0 4) DegreeTwoThreeSpectrum4695.graph sourceMap2407=true := by decide +kernel
theorem fusedMap2407_checked : acceptsGraphIso
    (fused (graph core2407) (root 9) 0 4) DegreeTwoThreeSpectrum4206.graph fusedMap2407=true := by decide +kernel
theorem certified2407 : Certified (graph core2407) (root 9) 0 4 :=
  of_native_maps core2407 DegreeTwoThreeSpectrum4695.graph DegreeTwoThreeSpectrum4206.graph
    sourceMap2407 fusedMap2407 sourceMap2407_checked fusedMap2407_checked
    DegreeTwoThreeFiniteComparisons.comparison2407
#print axioms sourceMap2407_checked
#print axioms fusedMap2407_checked
#print axioms certified2407
def sourceMap2407swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2407swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2407swap_checked : acceptsGraphIso
    (source (graph core2407) (root 9) 4 0) DegreeTwoThreeSpectrum4695.graph sourceMap2407swap=true := by decide +kernel
theorem fusedMap2407swap_checked : acceptsGraphIso
    (fused (graph core2407) (root 9) 4 0) DegreeTwoThreeSpectrum4206.graph fusedMap2407swap=true := by decide +kernel
theorem certified2407swap : Certified (graph core2407) (root 9) 4 0 :=
  of_native_maps core2407 DegreeTwoThreeSpectrum4695.graph DegreeTwoThreeSpectrum4206.graph
    sourceMap2407swap fusedMap2407swap sourceMap2407swap_checked fusedMap2407swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2407
#print axioms sourceMap2407swap_checked
#print axioms fusedMap2407swap_checked
#print axioms certified2407swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
