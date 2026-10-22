/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2385 : Family 9 := level9.get ⟨506,by decide⟩
def sourceMap2385 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2385 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2385_checked : acceptsGraphIso
    (source (graph core2385) (root 9) 0 4) DegreeTwoThreeSpectrum4587.graph sourceMap2385=true := by decide +kernel
theorem fusedMap2385_checked : acceptsGraphIso
    (fused (graph core2385) (root 9) 0 4) DegreeTwoThreeSpectrum4588.graph fusedMap2385=true := by decide +kernel
theorem certified2385 : Certified (graph core2385) (root 9) 0 4 :=
  of_native_maps core2385 DegreeTwoThreeSpectrum4587.graph DegreeTwoThreeSpectrum4588.graph
    sourceMap2385 fusedMap2385 sourceMap2385_checked fusedMap2385_checked
    DegreeTwoThreeFiniteComparisons.comparison2385
#print axioms sourceMap2385_checked
#print axioms fusedMap2385_checked
#print axioms certified2385
def sourceMap2385swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2385swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2385swap_checked : acceptsGraphIso
    (source (graph core2385) (root 9) 4 0) DegreeTwoThreeSpectrum4587.graph sourceMap2385swap=true := by decide +kernel
theorem fusedMap2385swap_checked : acceptsGraphIso
    (fused (graph core2385) (root 9) 4 0) DegreeTwoThreeSpectrum4588.graph fusedMap2385swap=true := by decide +kernel
theorem certified2385swap : Certified (graph core2385) (root 9) 4 0 :=
  of_native_maps core2385 DegreeTwoThreeSpectrum4587.graph DegreeTwoThreeSpectrum4588.graph
    sourceMap2385swap fusedMap2385swap sourceMap2385swap_checked fusedMap2385swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2385
#print axioms sourceMap2385swap_checked
#print axioms fusedMap2385swap_checked
#print axioms certified2385swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
