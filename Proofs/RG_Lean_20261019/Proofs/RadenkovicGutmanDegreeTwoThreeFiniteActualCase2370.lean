/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2370 : Family 9 := level9.get ⟨473,by decide⟩
def sourceMap2370 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2370 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2370_checked : acceptsGraphIso
    (source (graph core2370) (root 9) 0 4) DegreeTwoThreeSpectrum4507.graph sourceMap2370=true := by decide +kernel
theorem fusedMap2370_checked : acceptsGraphIso
    (fused (graph core2370) (root 9) 0 4) DegreeTwoThreeSpectrum4508.graph fusedMap2370=true := by decide +kernel
theorem certified2370 : Certified (graph core2370) (root 9) 0 4 :=
  of_native_maps core2370 DegreeTwoThreeSpectrum4507.graph DegreeTwoThreeSpectrum4508.graph
    sourceMap2370 fusedMap2370 sourceMap2370_checked fusedMap2370_checked
    DegreeTwoThreeFiniteComparisons.comparison2370
#print axioms sourceMap2370_checked
#print axioms fusedMap2370_checked
#print axioms certified2370
def sourceMap2370swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2370swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2370swap_checked : acceptsGraphIso
    (source (graph core2370) (root 9) 4 0) DegreeTwoThreeSpectrum4507.graph sourceMap2370swap=true := by decide +kernel
theorem fusedMap2370swap_checked : acceptsGraphIso
    (fused (graph core2370) (root 9) 4 0) DegreeTwoThreeSpectrum4508.graph fusedMap2370swap=true := by decide +kernel
theorem certified2370swap : Certified (graph core2370) (root 9) 4 0 :=
  of_native_maps core2370 DegreeTwoThreeSpectrum4507.graph DegreeTwoThreeSpectrum4508.graph
    sourceMap2370swap fusedMap2370swap sourceMap2370swap_checked fusedMap2370swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2370
#print axioms sourceMap2370swap_checked
#print axioms fusedMap2370swap_checked
#print axioms certified2370swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
