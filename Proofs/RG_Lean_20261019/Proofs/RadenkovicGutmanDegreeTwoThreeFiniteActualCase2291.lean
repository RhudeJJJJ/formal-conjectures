/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2291 : Family 9 := level9.get ⟨272,by decide⟩
def sourceMap2291 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2291 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2291_checked : acceptsGraphIso
    (source (graph core2291) (root 9) 0 4) DegreeTwoThreeSpectrum4605.graph sourceMap2291=true := by decide +kernel
theorem fusedMap2291_checked : acceptsGraphIso
    (fused (graph core2291) (root 9) 0 4) DegreeTwoThreeSpectrum4085.graph fusedMap2291=true := by decide +kernel
theorem certified2291 : Certified (graph core2291) (root 9) 0 4 :=
  of_native_maps core2291 DegreeTwoThreeSpectrum4605.graph DegreeTwoThreeSpectrum4085.graph
    sourceMap2291 fusedMap2291 sourceMap2291_checked fusedMap2291_checked
    DegreeTwoThreeFiniteComparisons.comparison2291
#print axioms sourceMap2291_checked
#print axioms fusedMap2291_checked
#print axioms certified2291
def sourceMap2291swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2291swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2291swap_checked : acceptsGraphIso
    (source (graph core2291) (root 9) 4 0) DegreeTwoThreeSpectrum4605.graph sourceMap2291swap=true := by decide +kernel
theorem fusedMap2291swap_checked : acceptsGraphIso
    (fused (graph core2291) (root 9) 4 0) DegreeTwoThreeSpectrum4085.graph fusedMap2291swap=true := by decide +kernel
theorem certified2291swap : Certified (graph core2291) (root 9) 4 0 :=
  of_native_maps core2291 DegreeTwoThreeSpectrum4605.graph DegreeTwoThreeSpectrum4085.graph
    sourceMap2291swap fusedMap2291swap sourceMap2291swap_checked fusedMap2291swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2291
#print axioms sourceMap2291swap_checked
#print axioms fusedMap2291swap_checked
#print axioms certified2291swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
