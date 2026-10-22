/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2436 : Family 9 := level9.get ⟨635,by decide⟩
def sourceMap2436 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2436 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2436_checked : acceptsGraphIso
    (source (graph core2436) (root 9) 0 4) DegreeTwoThreeSpectrum4792.graph sourceMap2436=true := by decide +kernel
theorem fusedMap2436_checked : acceptsGraphIso
    (fused (graph core2436) (root 9) 0 4) DegreeTwoThreeSpectrum4397.graph fusedMap2436=true := by decide +kernel
theorem certified2436 : Certified (graph core2436) (root 9) 0 4 :=
  of_native_maps core2436 DegreeTwoThreeSpectrum4792.graph DegreeTwoThreeSpectrum4397.graph
    sourceMap2436 fusedMap2436 sourceMap2436_checked fusedMap2436_checked
    DegreeTwoThreeFiniteComparisons.comparison2436
#print axioms sourceMap2436_checked
#print axioms fusedMap2436_checked
#print axioms certified2436
def sourceMap2436swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2436swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2436swap_checked : acceptsGraphIso
    (source (graph core2436) (root 9) 4 0) DegreeTwoThreeSpectrum4792.graph sourceMap2436swap=true := by decide +kernel
theorem fusedMap2436swap_checked : acceptsGraphIso
    (fused (graph core2436) (root 9) 4 0) DegreeTwoThreeSpectrum4397.graph fusedMap2436swap=true := by decide +kernel
theorem certified2436swap : Certified (graph core2436) (root 9) 4 0 :=
  of_native_maps core2436 DegreeTwoThreeSpectrum4792.graph DegreeTwoThreeSpectrum4397.graph
    sourceMap2436swap fusedMap2436swap sourceMap2436swap_checked fusedMap2436swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2436
#print axioms sourceMap2436swap_checked
#print axioms fusedMap2436swap_checked
#print axioms certified2436swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
