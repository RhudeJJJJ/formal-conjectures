/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2421 : Family 9 := level9.get ⟨594,by decide⟩
def sourceMap2421 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2421 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2421_checked : acceptsGraphIso
    (source (graph core2421) (root 9) 0 4) DegreeTwoThreeSpectrum4727.graph sourceMap2421=true := by decide +kernel
theorem fusedMap2421_checked : acceptsGraphIso
    (fused (graph core2421) (root 9) 0 4) DegreeTwoThreeSpectrum4270.graph fusedMap2421=true := by decide +kernel
theorem certified2421 : Certified (graph core2421) (root 9) 0 4 :=
  of_native_maps core2421 DegreeTwoThreeSpectrum4727.graph DegreeTwoThreeSpectrum4270.graph
    sourceMap2421 fusedMap2421 sourceMap2421_checked fusedMap2421_checked
    DegreeTwoThreeFiniteComparisons.comparison2421
#print axioms sourceMap2421_checked
#print axioms fusedMap2421_checked
#print axioms certified2421
def sourceMap2421swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2421swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2421swap_checked : acceptsGraphIso
    (source (graph core2421) (root 9) 4 0) DegreeTwoThreeSpectrum4727.graph sourceMap2421swap=true := by decide +kernel
theorem fusedMap2421swap_checked : acceptsGraphIso
    (fused (graph core2421) (root 9) 4 0) DegreeTwoThreeSpectrum4270.graph fusedMap2421swap=true := by decide +kernel
theorem certified2421swap : Certified (graph core2421) (root 9) 4 0 :=
  of_native_maps core2421 DegreeTwoThreeSpectrum4727.graph DegreeTwoThreeSpectrum4270.graph
    sourceMap2421swap fusedMap2421swap sourceMap2421swap_checked fusedMap2421swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2421
#print axioms sourceMap2421swap_checked
#print axioms fusedMap2421swap_checked
#print axioms certified2421swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
