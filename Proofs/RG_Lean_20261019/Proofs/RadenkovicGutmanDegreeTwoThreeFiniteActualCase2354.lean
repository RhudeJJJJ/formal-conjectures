/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2354 : Family 9 := level9.get ⟨434,by decide⟩
def sourceMap2354 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2354 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2354_checked : acceptsGraphIso
    (source (graph core2354) (root 9) 0 4) DegreeTwoThreeSpectrum4430.graph sourceMap2354=true := by decide +kernel
theorem fusedMap2354_checked : acceptsGraphIso
    (fused (graph core2354) (root 9) 0 4) DegreeTwoThreeSpectrum4431.graph fusedMap2354=true := by decide +kernel
theorem certified2354 : Certified (graph core2354) (root 9) 0 4 :=
  of_native_maps core2354 DegreeTwoThreeSpectrum4430.graph DegreeTwoThreeSpectrum4431.graph
    sourceMap2354 fusedMap2354 sourceMap2354_checked fusedMap2354_checked
    DegreeTwoThreeFiniteComparisons.comparison2354
#print axioms sourceMap2354_checked
#print axioms fusedMap2354_checked
#print axioms certified2354
def sourceMap2354swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2354swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2354swap_checked : acceptsGraphIso
    (source (graph core2354) (root 9) 4 0) DegreeTwoThreeSpectrum4430.graph sourceMap2354swap=true := by decide +kernel
theorem fusedMap2354swap_checked : acceptsGraphIso
    (fused (graph core2354) (root 9) 4 0) DegreeTwoThreeSpectrum4431.graph fusedMap2354swap=true := by decide +kernel
theorem certified2354swap : Certified (graph core2354) (root 9) 4 0 :=
  of_native_maps core2354 DegreeTwoThreeSpectrum4430.graph DegreeTwoThreeSpectrum4431.graph
    sourceMap2354swap fusedMap2354swap sourceMap2354swap_checked fusedMap2354swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2354
#print axioms sourceMap2354swap_checked
#print axioms fusedMap2354swap_checked
#print axioms certified2354swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
