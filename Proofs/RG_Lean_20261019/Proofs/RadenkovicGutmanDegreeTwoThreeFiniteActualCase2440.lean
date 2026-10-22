/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2440 : Family 9 := level9.get ⟨642,by decide⟩
def sourceMap2440 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2440 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2440_checked : acceptsGraphIso
    (source (graph core2440) (root 9) 0 4) DegreeTwoThreeSpectrum4801.graph sourceMap2440=true := by decide +kernel
theorem fusedMap2440_checked : acceptsGraphIso
    (fused (graph core2440) (root 9) 0 4) DegreeTwoThreeSpectrum4414.graph fusedMap2440=true := by decide +kernel
theorem certified2440 : Certified (graph core2440) (root 9) 0 4 :=
  of_native_maps core2440 DegreeTwoThreeSpectrum4801.graph DegreeTwoThreeSpectrum4414.graph
    sourceMap2440 fusedMap2440 sourceMap2440_checked fusedMap2440_checked
    DegreeTwoThreeFiniteComparisons.comparison2440
#print axioms sourceMap2440_checked
#print axioms fusedMap2440_checked
#print axioms certified2440
def sourceMap2440swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2440swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2440swap_checked : acceptsGraphIso
    (source (graph core2440) (root 9) 4 0) DegreeTwoThreeSpectrum4801.graph sourceMap2440swap=true := by decide +kernel
theorem fusedMap2440swap_checked : acceptsGraphIso
    (fused (graph core2440) (root 9) 4 0) DegreeTwoThreeSpectrum4414.graph fusedMap2440swap=true := by decide +kernel
theorem certified2440swap : Certified (graph core2440) (root 9) 4 0 :=
  of_native_maps core2440 DegreeTwoThreeSpectrum4801.graph DegreeTwoThreeSpectrum4414.graph
    sourceMap2440swap fusedMap2440swap sourceMap2440swap_checked fusedMap2440swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2440
#print axioms sourceMap2440swap_checked
#print axioms fusedMap2440swap_checked
#print axioms certified2440swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
