/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2383 : Family 9 := level9.get ⟨503,by decide⟩
def sourceMap2383 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2383 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2383_checked : acceptsGraphIso
    (source (graph core2383) (root 9) 0 4) DegreeTwoThreeSpectrum4581.graph sourceMap2383=true := by decide +kernel
theorem fusedMap2383_checked : acceptsGraphIso
    (fused (graph core2383) (root 9) 0 4) DegreeTwoThreeSpectrum4582.graph fusedMap2383=true := by decide +kernel
theorem certified2383 : Certified (graph core2383) (root 9) 0 4 :=
  of_native_maps core2383 DegreeTwoThreeSpectrum4581.graph DegreeTwoThreeSpectrum4582.graph
    sourceMap2383 fusedMap2383 sourceMap2383_checked fusedMap2383_checked
    DegreeTwoThreeFiniteComparisons.comparison2383
#print axioms sourceMap2383_checked
#print axioms fusedMap2383_checked
#print axioms certified2383
def sourceMap2383swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2383swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2383swap_checked : acceptsGraphIso
    (source (graph core2383) (root 9) 4 0) DegreeTwoThreeSpectrum4581.graph sourceMap2383swap=true := by decide +kernel
theorem fusedMap2383swap_checked : acceptsGraphIso
    (fused (graph core2383) (root 9) 4 0) DegreeTwoThreeSpectrum4582.graph fusedMap2383swap=true := by decide +kernel
theorem certified2383swap : Certified (graph core2383) (root 9) 4 0 :=
  of_native_maps core2383 DegreeTwoThreeSpectrum4581.graph DegreeTwoThreeSpectrum4582.graph
    sourceMap2383swap fusedMap2383swap sourceMap2383swap_checked fusedMap2383swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2383
#print axioms sourceMap2383swap_checked
#print axioms fusedMap2383swap_checked
#print axioms certified2383swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
